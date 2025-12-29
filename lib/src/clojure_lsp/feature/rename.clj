(ns clojure-lsp.feature.rename
  (:require
   [clojure-lsp.parser :as parser]
   [clojure-lsp.queries :as q]
   [clojure-lsp.refactor.edit :as edit]
   [clojure-lsp.settings :as settings]
   [clojure-lsp.shared :as shared]
   [clojure.string :as string]
   [medley.core :as medley]
   [rewrite-clj.zip :as z]))

(set! *warn-on-reflection* true)

(defn ident-split [ident-str]
  (let [ident-conformed (some-> ident-str (string/replace #"^::?" ""))
        prefix          (string/replace ident-str #"^(::?)?.*" "$1")
        idx             (string/index-of ident-conformed "/")]
    (if (and idx (not= idx (dec (count ident-conformed))))
      (into [prefix] (string/split ident-conformed #"/" 2))
      [prefix nil ident-conformed])))

(defn ^:private rename-other
  [replacement db reference]
  (let [name-start (- (:name-end-col reference) (count (name (:name reference))))
        ref-doc-uri (:uri reference)
        version (get-in db [:documents ref-doc-uri :v] 0)]
    {:range (shared/->range (assoc reference :name-col name-start))
     :new-text replacement
     :text-document {:version version :uri ref-doc-uri}}))

(defn ^:private rename-keyword
  [replacement
   replacement-raw
   db
   {:keys [ns alias name uri
           name-col name-end-col
           namespace-from-prefix
           keys-destructuring] :as reference}]
  (let [version (get-in db [:documents uri :v] 0)
        ;; Infers if the qualified keyword is of the ::kw-name kind
        ;; So the same-ns style or the full qualified name can be preserved
        ;; The 2 accounts for the 2 colons in same-namespace qualified keyword
        qualified-same-ns? (= (- name-end-col name-col)
                              (+ 2 (count name)))
        ;; Extracts the name of the keyword
        ;; Maybe have the replacement analyzed by clj-kondo instead?
        replacement-name (string/replace replacement #":+(.+/)?" "")
        ;; Extracts the namespace of the keyword
        ;; Maybe have the replacement analyzed by clj-kondo instead?
        replacement-ns (string/replace replacement-raw #":+(.+)/.+" "$1")
        namespace-changed? (and ns
                                replacement-ns
                                ;; allow only simple namespaced keywords, not aliased keywords
                                (re-matches #"^:(.+)/.+" replacement-raw))
        ;; we find the locals analysis since when destructuring we have both
        ;; keyword and a locals analysis for the same position
        local-element (when keys-destructuring
                        (q/find-local-by-destructured-keyword db uri reference))
        text (cond
               (and local-element
                    (string/includes? (:str local-element) "/")
                    (string/starts-with? (:str local-element) ":"))
               (str ":" ns "/" replacement-name)

               (and local-element
                    (string/includes? (:str local-element) "/"))
               (str ns "/" replacement-name)

               local-element
               replacement-name

               alias
               (str "::" alias "/" replacement-name)

               (and qualified-same-ns?
                    ;; check if it is from aliased keyword -> namespaced keyword
                    (string/starts-with? replacement-raw "::"))
               (str "::" replacement-name)

               (and qualified-same-ns?
                    ;; check if is from aliased keyword -> namespaced keyword
                    (string/starts-with? replacement-raw ":"))
               replacement-raw

               namespace-from-prefix
               (str ":" replacement-name)

               namespace-changed?
               (str ":" replacement-ns "/" replacement-name)

               ns
               (str ":" ns "/" replacement-name)

               ;; There shouldn't be another case, since renaming
               ;; unqualified keywords is currently disallowed
               :else
               replacement)]
    (concat
      [{:range (shared/->range reference)
        :new-text text
        :text-document {:version version :uri uri}}]
      (when local-element
        (->> (q/find-references db local-element false)
             (map (fn [reference]
                    {:range (shared/->range reference)
                     :new-text replacement-name
                     :text-document {:version version :uri uri}})))))))

(defn ^:private rename-ns-definition [replacement db reference]
  (let [ref-doc-uri (:uri reference)
        version (get-in db [:documents ref-doc-uri :v] 0)
        text (if (contains? #{:keyword-definitions :keyword-usages} (:bucket reference))
               (str ":" replacement "/" (:name reference))
               replacement)]
    {:range (shared/->range reference)
     :new-text text
     :text-document {:version version :uri ref-doc-uri}}))

(defn ^:private rename-alias-definition [replacement db reference]
  (let [alias? (= :namespace-alias (:bucket reference))
        keyword? (contains? #{:keyword-definitions :keyword-usages} (:bucket reference))
        ref-doc-uri (:uri reference)
        [u-prefix _ u-name] (when-not alias?
                              (ident-split (:name reference)))
        version (get-in db [:documents ref-doc-uri :v] 0)]
    (if keyword?
      {:range (shared/->range reference)
       :new-text (str "::" replacement "/" (:name reference))
       :text-document {:version version :uri ref-doc-uri}}
      {:range (shared/->range reference)
       :new-text (if alias? replacement (str u-prefix replacement "/" u-name))
       :text-document {:version version :uri ref-doc-uri}})))

(defn ^:private rename-usages-with-alias
  [{:keys [uri] :as element} replacement replacement-raw db references]
  (let [new-alias (first (string/split replacement-raw #"/"))
        old-alias (:alias (first (filter #(and (:alias %)
                                               (= uri (:uri %))) references)))
        alias-definition (q/find-namespace-alias-by-alias db uri old-alias)]
    (conj
      (mapv (fn [reference]
              (cond
                (= element reference)
                {:range (shared/->range reference)
                 :new-text replacement-raw
                 :text-document {:version (get-in db [:documents uri :v] 0) :uri uri}}

                (and (= (:uri reference) uri)
                     (:alias reference))
                {:range (shared/->range reference)
                 :new-text replacement-raw
                 :text-document {:version (get-in db [:documents (:uri reference) :v] 0) :uri (:uri reference)}}

                :else
                (rename-other replacement db reference))) references)
      (rename-alias-definition new-alias db alias-definition))))

(defn ^:private rename-local
  [replacement db reference]
  (let [name-start (- (:name-end-col reference) (count (name (:name reference))))
        ref-doc-uri (:uri reference)
        version (get-in db [:documents ref-doc-uri :v] 0)]
    (if (string/starts-with? replacement ":")
      {:range (shared/->range (assoc reference
                                     :name-col name-start))
       :new-text (subs replacement 1)
       :text-document {:version version :uri ref-doc-uri}}
      {:range (shared/->range (assoc reference :name-col name-start))
       :new-text replacement
       :text-document {:version version :uri ref-doc-uri}})))

(defn ^:private rename-defrecord
  [replacement db reference]
  (let [current-name (str (:name reference))
        map->? (string/starts-with? current-name "map->")
        ->? (string/starts-with? current-name "->")
        name-col (if (:alias reference)
                   (+ (:name-col reference) (inc (count (str (:alias reference)))))
                   (:name-col reference))
        name-end (+ name-col (count (name current-name)))
        ref-doc-uri (:uri reference)
        version (get-in db [:documents ref-doc-uri :v] 0)]
    {:new-text (cond
                 map->?
                 (str "map->" replacement)

                 ->?
                 (str "->" replacement)

                 :else
                 replacement)
     :text-document {:version version :uri ref-doc-uri}
     :range (shared/->range (assoc reference
                                   :name-col name-col
                                   :name-end-col name-end))}))

(defn ^:private rename-changes
  [element definition references replacement replacement-raw db]
  (cond
    (identical? :namespace-alias (:bucket element))
    (mapv (partial rename-alias-definition replacement db) references)

    (and (identical? :var-usages (:bucket element))
         (string/includes? replacement-raw "/"))
    (rename-usages-with-alias element replacement replacement-raw db references)

    (identical? :namespace-definitions (:bucket definition))
    (mapv (partial rename-ns-definition replacement db) references)

    (contains? #{:keyword-definitions :keyword-usages} (:bucket definition))
    (vec (mapcat (partial rename-keyword replacement replacement-raw db) references))

    (identical? :locals (:bucket definition))
    (mapv (partial rename-local replacement db) references)

    (and (identical? :var-definitions (:bucket definition))
         (some '#{clojure.core/defrecord cljs.core/defrecord}
               (q/defined-bys definition)))
    (->> references
         (remove #(and (identical? :var-definitions (:bucket %))
                       (or (string/starts-with? (str (:name %)) "->")
                           (string/starts-with? (str (:name %)) "map->"))))
         (mapv (partial rename-defrecord replacement db)))

    :else
    (mapv (partial rename-other replacement db) references)))

(defn ^:private element-name-range
  [element]
  {:name-row (or (:name-row element) (:row element))
   :name-col (or (:name-col element) (:col element))
   :name-end-row (or (:name-end-row element) (:end-row element))
   :name-end-col (or (:name-end-col element) (:end-col element))})

(defn ^:private cursor-token-at-position
  [db uri row col]
  (when-let [zloc (some-> (parser/safe-zloc-of-file db uri)
                          (edit/find-at-pos row col))]
    (when (identical? :token (z/tag zloc))
      (let [{:keys [row col end-row end-col] :as node-meta} (meta (z/node zloc))
            token-str (z/string zloc)
            token-sexpr (parser/safe-zloc-sexpr zloc)
            token-name (when (symbol? token-sexpr)
                         (name token-sexpr))]
        (when (and row col end-row end-col)
          {:text token-str
           :name token-name
           :range (shared/->range {:row row
                                   :col col
                                   :end-row end-row
                                   :end-col end-col})
           :pos (select-keys node-meta [:row :col :end-row :end-col])})))))

(defn ^:private reference->substring-edit
  [replacement old-name db reference]
  (let [ref-name (name (:name reference))
        new-text (string/replace ref-name old-name replacement)]
    (when (and (not (string/blank? old-name))
               (not= ref-name new-text))
      (let [name-end-col (or (:name-end-col reference) (:end-col reference))
            name-start (- name-end-col (count ref-name))
            ref-doc-uri (:uri reference)
            version (get-in db [:documents ref-doc-uri :v] 0)]
        {:range (shared/->range (assoc reference :name-col name-start))
         :new-text new-text
         :text-document {:version version :uri ref-doc-uri}}))))

(defn ^:private existing-edit-keys
  [edits]
  (into #{}
        (map (fn [{:keys [range text-document]}]
               [(:uri text-document) range]))
        edits))

(defn ^:private existing-edit-ranges-by-uri
  [edits]
  (reduce (fn [acc {:keys [range text-document]}]
            (update acc (:uri text-document) (fnil conj []) range))
          {}
          edits))

(defn ^:private pos<=
  [{line-a :line char-a :character} {line-b :line char-b :character}]
  (or (< line-a line-b)
      (and (= line-a line-b) (<= char-a char-b))))

(defn ^:private range-before?
  [range-a range-b]
  (let [end-a (:end range-a)
        start-b (:start range-b)]
    (pos<= end-a start-b)))

(defn ^:private range-overlaps?
  [range-a range-b]
  (not (or (range-before? range-a range-b)
           (range-before? range-b range-a))))

(defn ^:private reference-name
  [reference]
  (some-> (:name reference) name))

(defn ^:private substring-reference?
  [old-name reference]
  (let [ref-name (reference-name reference)]
    (and (string? old-name)
         (not (string/blank? old-name))
         ref-name
         (string/includes? ref-name old-name)
         (not= ref-name old-name))))

(defn ^:private common-prefix
  [strings]
  (let [non-empty (remove string/blank? strings)]
    (if (seq non-empty)
      (reduce
        (fn [prefix s]
          (let [limit (min (count prefix) (count s))]
            (loop [idx 0]
              (if (or (= idx limit)
                      (not= (nth prefix idx) (nth s idx)))
                (subs prefix 0 idx)
                (recur (inc idx))))))
        (first non-empty)
        (rest non-empty))
      "")))

(defn ^:private infer-old-name
  [references definition cursor-token]
  (let [ref-names (keep (fn [reference]
                          (some-> (:name reference) name))
                        references)
        cursor-name (:name cursor-token)
        cursor-text (:text cursor-token)
        cursor-candidate (or cursor-name cursor-text)
        cursor-candidate (when (and (string? cursor-candidate)
                                    (not (string/blank? cursor-candidate))
                                    (some #(string/includes? % cursor-candidate) ref-names))
                           cursor-candidate)
        prefix (common-prefix ref-names)
        def-name (some-> definition :name name)]
    (first (remove string/blank? [cursor-candidate prefix def-name]))))

(defn ^:private substring-edit-pairs
  [old-name replacement db references]
  (->> references
       (filter #(contains? #{:var-usages :symbols} (:bucket %)))
       (filter #(substring-reference? old-name %))
       (keep (fn [reference]
               (when-let [edit (reference->substring-edit replacement old-name db reference)]
                 {:reference-range (shared/->range reference)
                  :edit edit})))
       vec))

(defn ^:private match-substring-edit-index
  [pairs used change]
  (first
    (keep-indexed (fn [idx {:keys [reference-range]}]
                    (when (and (not (contains? used idx))
                               (range-overlaps? reference-range (:range change)))
                      idx))
                  pairs)))

(defn ^:private apply-substring-edits
  [changes substring-pairs]
  (let [[updated-changes used] (reduce (fn [[acc used] change]
                                         (if-let [idx (match-substring-edit-index substring-pairs used change)]
                                           [(conj acc (:edit (nth substring-pairs idx)))
                                            (conj used idx)]
                                           [(conj acc change) used]))
                                       [[] #{}]
                                       changes)
        updated-changes (vec updated-changes)
        existing-keys (existing-edit-keys updated-changes)
        remaining (->> (map-indexed vector substring-pairs)
                       (remove #(contains? used (first %)))
                       (map (comp :edit second))
                       (remove (fn [{:keys [range text-document]}]
                                 (contains? existing-keys [(:uri text-document) range]))))]
    (into updated-changes remaining)))

(defn ^:private cursor-token-edit
  [cursor-token old-name replacement db uri existing-edits]
  (when (and cursor-token
             (string? old-name)
             (not (string/blank? old-name))
             (string? replacement)
             (not= old-name replacement))
    (let [{:keys [range]} cursor-token
          existing-ranges-by-uri (existing-edit-ranges-by-uri existing-edits)
          edit {:range range
                :new-text replacement
                :text-document {:version (get-in db [:documents uri :v] 0)
                                :uri uri}}]
      (when-not (some #(range-overlaps? % range) (get existing-ranges-by-uri uri))
        edit))))

(defn ^:private rename-status
  ([db element]
   (rename-status db element nil nil))
  ([db element references definition]
   (let [references (or references (q/find-references db element true))
         definition (or definition (q/find-definition db element))
        client-capabilities (:client-capabilities db)
        source-paths (settings/get db [:source-paths])
        source-path (some-> (:uri definition)
                            (shared/uri->source-path source-paths))]
    (cond
      (not definition)
      {:error {:message "Can't rename - no definition found."
               :code :invalid-params}}

      (empty? references)
      {:error {:message "Can't rename - no other references found."
               :code :invalid-params}}

      (and (= :namespace-definitions (:bucket definition))
           (not= :namespace-alias (:bucket element))
           (not source-path))
      {:error {:code :invalid-params
               :message "Can't rename - invalid source-paths. Are project :source-paths configured correctly?"}}

      (and (= :namespace-definitions (:bucket definition))
           (not= :namespace-alias (:bucket element))
           (not (get-in client-capabilities [:workspace :workspace-edit :document-changes])))
      {:error {:code :invalid-params
               :message "Can't rename - client does not support file renames."}}

      (and (= :namespace-definitions (:bucket definition))
           (not= :namespace-alias (:bucket element))
           (not= 1 (count (q/find-all-project-namespace-definitions db (:name definition)))))
      {:error {:code :invalid-params
               :message "Can't rename - namespace is defined in multiple files."}}

      (and (contains? #{:keyword-definitions :keyword-usages} (:bucket definition))
           (not (:ns definition)))
      {:error {:code :invalid-params
               :message "Can't rename - only namespaced keywords can be renamed."}}

      :else
      {:result :success
       :references references
       :definition definition
       :source-path source-path}))))

(def ^:private error-no-element
  {:error {:code :invalid-params
           :message "Can't rename - no element found."}})

(defn prepare-rename
  [uri row col db]
  (let [element (q/find-element-under-cursor db uri row col)]
    (if-not element
      error-no-element
      (let [{:keys [error] :as result} (rename-status db element)]
        (if error
          result
          (shared/->range element))))))

(defn rename-element
  ([new-name db element source]
   (rename-element new-name db element source nil))
  ([new-name db element source cursor-token]
   (let [{:keys [row col]} (:pos cursor-token)
         cursor-elements (when (and cursor-token (= source :rename) row col)
                           (q/find-all-elements-under-cursor db (:uri element) row col))
         var-def-elements (filter #(identical? :var-definitions (:bucket %)) cursor-elements)
         cursor-references (when (and (< 1 (count var-def-elements)) row col)
                             (q/find-references-from-cursor db (:uri element) row col true))
         {:keys [error] :as result} (rename-status db element cursor-references nil)]
     (if error
       result
       (let [{:keys [references definition source-path]} result
             replacement (string/replace new-name #".*/([^/]*)$" "$1")
             old-name (infer-old-name references definition cursor-token)
             references (if (and (string? old-name)
                                 (not (string/blank? old-name)))
                          (remove (fn [reference]
                                    (and (identical? :var-definitions (:bucket reference))
                                         (not= (reference-name reference) old-name)))
                                  references)
                          references)
             changes (rename-changes element definition references replacement new-name db)
             substring-pairs (when (and (string? old-name)
                                        (not (string/blank? old-name)))
                               (substring-edit-pairs old-name replacement db references))
             changes (if (seq substring-pairs)
                       (apply-substring-edits changes substring-pairs)
                       changes)
             token-edit (when (and cursor-token
                                   (string? old-name)
                                   (not (string/blank? old-name))
                                   (or (= old-name (:name cursor-token))
                                       (= old-name (:text cursor-token))))
                          (cursor-token-edit cursor-token old-name replacement db (:uri element) changes))
             changes (cond-> changes
                       token-edit (conj token-edit))
             doc-changes (->> changes
                              (group-by :text-document)
                              (remove (comp empty? val))
                              (map (fn [[text-document edits]]
                                     {:text-document text-document
                                      :edits (mapv #(dissoc % :text-document) edits)})))]
         (if (and (identical? :namespace-definitions (:bucket definition))
                  (not (identical? :namespace-alias (:bucket element)))
                  (not= :rename-file source))
           (let [def-uri (:uri definition)
                 file-type (shared/uri->file-type def-uri)
                 new-uri (shared/namespace->uri replacement source-path file-type db)]
             ;; We only add the rename file change as willRenameFiles request
             ;; will do the other changes
             (shared/client-changes (concat
                                      (when (:api? db) doc-changes)
                                      [{:kind "rename"
                                        :old-uri def-uri
                                        :new-uri new-uri}])
                                    db))
           (shared/client-changes doc-changes db)))))))

(defn rename-from-position
  [uri new-name row col db]
  (let [elements (q/find-all-elements-under-cursor db uri row col)
        element (or (first (filter #(identical? :var-definitions (:bucket %)) elements))
                    (first elements))]
    (if element
      (rename-element new-name db element :rename (cursor-token-at-position db uri row col))
      error-no-element)))
