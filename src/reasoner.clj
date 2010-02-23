(ns reasoner
 (:use clojure.set))

(defn new-graph
 []
 {:edges #{}})

(defn add-to-index
 [i k v]
 (let [o (i k #{})
       n (conj o v)]
   (assoc i k n)))

(defn make-explicit
  [edge]
  (with-meta edge {:source :explicit}))

(defn make-inferred
  [edge]
  (with-meta edge {:source :inferred}))

(defn tag-explicit
  "Tag an edge as explicit only if it is not tagged."
  [edge]
  (with-meta edge {:source (:source (meta edge) :explicit)}))

(defn inferred?
  [edge]
  (= :inferred (:source (meta edge))))

(defn explicit?
  [edge]
  (let [source (:source (meta edge))]
   (or (nil? source)
       (= :explicit source))))

(defn add-edge
  [g stmt]
  {:edges (conj (:edges g) stmt)})

(defn build-graph
  [stmts]
  (reduce add-edge (new-graph) (map tag-explicit stmts)))

(defn query-single
  "Apply a restriction to the graph.
All edge elements i must be = to v.  If v
is nil, no restriction is applied."
  [g [i v]]
  (if (nil? v)
    g
    (build-graph (filter #(= (% i) v) (:edges g)))))

(defn query-edges
  [graph & args]
  (reduce #(query-single %1 %2) graph args))

(defn variable?
  [x]
  (and (symbol? x)
       (.startsWith (str x) "?")))

(defn vars
  [stmt]
  (for [[idx var] stmt :when (variable? var)] [idx var]))

(defn non-vars
  [stmt]
  (for [[idx val] stmt :when (not (variable? val))] [idx val]))

(defn rehash
  [s]
  (apply hash-map (apply concat s)))



;;; a solution is a set of bindings and a graph that matches that binding
;;; a statement is an edge with optional parts and variable parts
(defn gensols
 [graph stmt]
 (let [	;; vars get bound to values
       vars (vars stmt)
       ;; non-vars are values that must match in the graph
       non-vars (non-vars stmt)
       ;; 
       edges (apply query-edges graph non-vars)]
   (set (for [edge (:edges edges)]
          {:graph (build-graph [edge])
           :bindings (rehash (for [[idx var] vars]
			       [var (edge idx)]))}))))

(defn merge-graphs
  [g1 g2]
  (reduce add-edge g1 (:edges g2)))

(defn all-true
  [es]
  (every? identity es))

(defn combine-sols
  [s1 s2]
  (if (all-true (for [[k v] (:bindings s1) :when ((:bindings s2) k)]
			 (= v ((:bindings s2) k))))
    {:bindings (merge (:bindings s1) (:bindings s2))
     :graph (merge-graphs (:graph s1)
			  (:graph s2))}))

(defn cross
  [f l1 l2]
  (for [a l1 b l2]
    (f a b)))

(defn q
  [g sols stmt]
  (set (filter #(not (nil? %)) (cross combine-sols sols (gensols g stmt)))))

(defn query-old
 [graph stmts]
 (reduce #(q graph %1 %2)
	 #{{:graph (new-graph) :bindings {}}}
	 stmts))

(defn edge-stmt?
  [stmt]
  (map? stmt))

(defn expr-stmt?
  [stmt]
  (not (edge-stmt? stmt)))

(defn make-expr
  [vars & body]
  (eval `(fn [~@vars] ~@body)))

(defn sol-valid
  [sol expr]
  (let [vars (map first (:bindings sol))
	vals (map second (:bindings sol))
	f (apply make-expr vars expr)]
    (apply f vals)))

(defn sol-valid-all
  [sol exprs]
  (all-true (map #(sol-valid sol %) exprs)))

(defn query
  [graph stmts]
  (let [edge-stmts (filter edge-stmt? stmts)
	expr-stmts (filter expr-stmt? stmts)
	sols (query-old graph edge-stmts)]
    (set (filter #(sol-valid-all % expr-stmts) sols))))


(def test-graph
     (build-graph [
		   {:s "George" :r "type" :o "Person"}
		   {:s "John" :r "type" :o "Person"}
		   {:s "Susie" :r "type" :o "Person"}
		   {:s "George" :r "hasGirlfriend" :o "Susie"}
		   {:s "Banana" :r "type" :o "Fruit"}
		   {:s "George" :r "likes" :o "Banana"}
		   {:s "Susie" :r "likes" :o "Apple"}
		   {:s "John" :r "hasGirlfriend" :o "Linda"}
		   {:s "Linda" :r "type" :o "Person"}
		   {:s "Apple" :r "type" :o "Fruit"}]))

(def t1 (query test-graph [{:s '?p :r "type" :o "Person"}]))
(def t2 (query test-graph [{:s '?bf :r "hasGirlfriend" :o '?gf}]))
(def t25 (query test-graph [{:s '?gf :r "likes" :o '?fruit}]))
(def t3 (query test-graph [{:s '?bf :r "hasGirlfriend" :o '?gf}
			   {:s '?gf :r "likes" :o '?fruit}
			   
			   {:s '?fruit :r "type" :o "Fruit"}]))

(defn rebind
  [stmnt bindings]
  (let [vars (vars stmnt)
	non-vars (non-vars stmnt)]
    (rehash (concat non-vars (for [[idx var] vars] [idx (bindings var)])))))

(defn rebind-all
  [stmnts bindings]
  (map #(rebind % bindings) stmnts))

(defn infer
  [graph ante conce]
  (loop [results (query graph ante) g graph]
    (if (seq results)
	 (let [r (first results)
	       c (map make-inferred (rebind-all conce (:bindings r)))]
	   (recur (rest results) (merge-graphs g {:edges (set c)})))
	 g)))

(defn infer-closure
  [graph ante conce]
  (loop [g-old graph g (infer graph ante conce)]
    (if (= g g-old)
      g
      (recur g (infer g ante conce)))))

;; a rule is [ante conse]
(defn infer-all
  [graph rules]
  (loop [rules rules g graph]
    (if (seq rules)
      (recur (rest rules) (apply infer-closure g (first rules)))
      g)))

;; infer the transitive closure of the graph and rules
(defn infer-all-closure
  [graph rules]
  (loop [g-old graph g (infer-all graph rules)]
    (if (= g g-old)
      (recur g (infer-all graph rules))
      g)))

;; example

;; a graph of explicit friendship relations
(def friends-graph 
     (build-graph [{:s "Andrew" :r "hasFriend" :o "John"}
		   {:s "Chris" :r "hasFriend" :o "Andrew"}
		   {:s "Jane" :r "hasFriend" :o "Linda"}
		   {:s "Jane" :r "hasFriend" :o "Chris"}]))

(def jane-s-friends
     (query friends-graph [{:s "Jane" :r "hasFriend" :o '?f}]))
;; => #{{:bindings {?f "Linda"}, :graph {:edges #{{:s "Jane", :r "hasFriend", :o "Linda"}}}} {:bindings {?f "Chris"}, :graph {:edges #{{:s "Jane", :r "hasFriend", :o "Chris"}}}}}
;; two solutions Linda and Chris

;; some rules

;; friendship is symmetrical
(def friend-symm
     [[{:s '?p :r "hasFriend" :o '?f}] 
      [{:s '?f :r "hasFriend" :o '?p}]])

;; friendship is transitive
(def friend-trans
     [[{:s '?p :r "hasFriend" :o '?q}
       {:s '?q :r "hasFriend" :o '?r}
       '(not (= ?p ?r))]
      [{:s '?p :r "hasFriend" :o '?r}]])

(def all-friends-graph (infer-all-closure friends-graph [friend-symm friend-trans]))

(def jane-s-friends-all
     (query all-friends-graph [{:s "Jane" :r "hasFriend" :o '?f}]))
;; => #{{:bindings {?f "Linda"}, :graph {:edges #{{:s "Jane", :r "hasFriend", :o "Linda"}}}} {:bindings {?f "Jane"}, :graph {:edges #{{:r "hasFriend", :o "Jane", :s "Jane"}}}} {:bindings {?f "Andrew"}, :graph {:edges #{{:r "hasFriend", :o "Andrew", :s "Jane"}}}} {:bindings {?f "Chris"}, :graph {:edges #{{:s "Jane", :r "hasFriend", :o "Chris"}}}} {:bindings {?f "John"}, :graph {:edges #{{:r "hasFriend", :o "John", :s "Jane"}}}}}
;; 5 friends

(defn print-dot
  [graph]
  (let [edges (:edges graph)]
    (dorun (for [e edges]
	     (let [{:keys [s r o]} e
		   color (if (explicit? e)
			   "black"
			   "red")]
	       (println (str "edge [fontsize=\"9\" label=\"" r "\" color=\"" color "\"]"))
	       (println s "->" o))))))