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

(defn add-edge
  [g stmt]
  {:edges (conj (:edges g) stmt)})


(defn build-graph
  [stmts]
  (reduce add-edge 
	  (new-graph) 
	  stmts))

(defn query-single
  "Apply a restriction to the graph.  All edge elements i must be = to v.  If v
is nil, no restriction is applied."
  [g [p i v]]
 (if (nil? v)
   g
   (build-graph (filter #(p (% i) v) (:edges g)))))

(defn query-edges
 [g & args]
 (reduce #(query-single %1 %2) 
	 g 
	 args))

(defn variable?
 [x]
 (and (symbol? x)
      (.startsWith (str x) "?")))

(defn rehash
 [s]
 (apply hash-map (apply concat s)))

;;; a solution is a set of bindings and a graph that matches that binding
;;; a statement is an edge with optional parts and variable parts
(defn gensols
 [g stmt]
 (let [vars (filter #(variable? (% 1)) stmt)
       non-vars (apply concat (filter #(not (variable? (% 1))) stmt))
       edges (apply query-edges g non-vars)]
   (set (for [e (:edges edges)]
          {:graph (build-graph [e])
           :bindings (rehash (for [[k v] vars]
                                [v (e k)]))}))))

(defn merge-graphs
  [g1 g2]
  (reduce add-edge g1 (:edges g2)))

(defn combine-sols
 [s1 s2]
 (if (every? identity (for [[k v] (:bindings s1) :when ((:bindings s2) k)]
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

(defn query
 [g stmts]
 (reduce #(q g %1 %2)
	 #{{:graph (new-graph) :bindings {}}}
	 stmts))

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
