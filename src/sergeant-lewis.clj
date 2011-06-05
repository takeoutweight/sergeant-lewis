(ns sergeant-lewis
  (:use [chr]
        [chr.debug]
        [clojure.repl]
				[clojure.pprint])
  (:require [clojure.set :as set]
            [clojure.walk :as walk]
            #_[cljs.compiler :as comp]))

(defn errors
  "seq of the error messages in the type."
  [store]
  (fresh [_] (map #(get % _) (find-matches-recursive store [:Error _]))))

(declare narrowing-rules)
(declare deferred-narrowing-rules)
(declare widening-rules)

(defn combine-type-constraints
  "implements staged resolution, first positive constraints then the negative.
   operates on unwrapped (tuple-form) constraints"
  [& ts]
  (awake (concat narrowing-rules deferred-narrowing-rules)
         (unwrap (awake narrowing-rules {} ts))))

(defn combine-types
  "implements staged resolution, first positive constraints then the negative.
   operates on wrapped (nested set form) constraint stores."
  [t1 & ts]
  (awake (concat narrowing-rules deferred-narrowing-rules)
         (unwrap (awake narrowing-rules t1 (apply concat (map unwrap ts))))))

(defn incompatible? 
  "returns a seq of errors created by intersecting the type, or nil"
  [type1 type2]
  (let [old-errors (into #{} (concat (errors type1) (errors type2)))
        new-errors (set/difference (into #{} (errors (combine-types type1 type2)))
                                   old-errors)]
    (if (empty? new-errors)
      nil
      new-errors)))

(defn overlap?
  "do the types definitely overlap?
   i.e. do their constraints necessitate an overlap?"
  [type1 type2]
  (trace [:overlap?] [type1 type2])
  (let [merged (into #{} (concat (unwrap type1) (unwrap type2)))
        solved-store (combine-types type1 type2)
        solved (into #{} (unwrap solved-store))]
    (and (empty? (errors solved-store))
         (or (= type1 type2)
             (not= merged solved)))))

(def mutually-exclusive-types
  #{:Bool :Range :Keyword :Nil :Indexed :Fn})

(def narrowing-rules
  [#_(rule mutual-exclusion
           [:+ [T1 & _1]
            :- [T2 & _2]
            :when (and (mutually-exclusive-types T1)
                       ((set/difference mutually-exclusive-types #{T1}) T2))]
           [:Error (str "Mutually exclusive types: " T1 ", " T2)])
   (rule indexed
         [:- [:Indexed dom1 rng1]
          :- [:Indexed dom2 rng2]
          :when (not (incompatible? dom1 dom2))]
         [[:Indexed (awake widening-rules dom1 (unwrap dom2)) (combine-types rng1 rng2)]])
   
   (rule tuple
         [:+ [:Tuple a]
          :- [:Tuple b]]
         (if (= (count a) (count b))
           [[:Tuple (map (fn [p-a p-b] (combine-types p-a p-b))
                         a b)]]
           [[:Error (str "Conflicting Tuple arities: " a ", " b)]]))

   (rule java-types
         [:- [:OfClass c1]
          :- [:OfClass c2]
          :when (.isAssignableFrom c1 c2)]
         [[:OfClass c2]])
   (rule java-types2
         [:+ [:OfClass c1]
          :- [:OfClass c2]
          :when (not (.isInterface c1))
          :when (not (.isInterface c2))
          :when (not (or (.isAssignableFrom c1 c2)
                         (.isAssignableFrom c2 c1)))]
         [[:Error (str "class " c1 " is neither a supertype nor subtype of " c2)]])
   
   (rule range-lower-bound
         [:- [:Range m1 M1]
          :- [:Range m2 M2]
          :when (number? m1)
          :when (number? m2)]
         [[:Range (max m1 m2) M1]
          [:Range (max m1 m2) M2]])
   (rule range-upper-bound
         [:- [:Range m1 M1]
          :- [:Range m2 M2]
          :when (number? M1)
          :when (number? M2)]
         [[:Range m1 (min M1 M2)]
          [:Range m2 (min M1 M2)]])
   (rule empty-range
         [:- [:Range m M]
          :when (and (number? m)
                     (number? M)
                     (< M m))]
         [[:Error (str "Empty range: [" m ", " M "]")]])

   (rule lower-bound
         [:- [:Min m1]
          :- [:Min m2]
          :when (number? m1)
          :when (number? m2)]
         [[:Min (max m1 m2)]])
   (rule range-upper-bound
         [:- [:Max M1]
          :- [:Max M2]
          :when (number? M1)
          :when (number? M2)]
         [[:Max (min M1 M2)]
          [:Max (min M1 M2)]])
   (rule empty-range
         [:- [:Min m]
          :- [:Max M]
          :when (and (number? m)
                     (number? M)
                     (< M m))]
         [[:Error (str "Empty range: [" m ", " M "]")]])

   (rule simplify-negation
         [:- [:Not t1]]
         (for [t (awake widening-rules [[t1]])]
           [:Not t]))
   (rule combine-negation
         [:- [:Not t1]
          :- [:Not t2]]
         (for [t (awake widening-rules [[t1] [t2]])]
           [:Not t]))
   
   (rule simplify-union
         [:- [:Union ts]]
         [[:Union (awake widening-rules (unwrap ts))]])
   (rule combine-union
         [:- [:Union u1]
          :- [:Union u2]]
         [[:Union (set (for [t1 u1 t2 u2] (combine-types t1 t2)))]])
   #_"TODO: erase union types with errors"

   (rule value-type
         [:+ [a t1]
          :- [a t2]
          :when (#{:Class} a)
          :when (not= t1 t2)]
         [[:Error (str "not-equal: " t1 ", " t2 " for type constraint " a)]])])

(def deferred-narrowing-rules
  ;;tricky subtlety: The refected 'store' is w/o the matched [& any] constraint. (but we
  ;;need it to match on any positively asserted constraints) So we manually add it into wholestore.
  [(rule negation-conflict
         [:store store
          :+ [& any]
          :- [:Not t2]
          :let [wholestore (impose-constraint (dissoc store :Not) any)]
          :when (do (trace [:negation-conflict] ["any:" any "store:" store "t2:" t2]) (overlap? t2 wholestore))]
         [[:Error (str "Negation conflict, both " wholestore " and :Not " t2)]])])

(defn narrower?
  "is type-1 necessarily narrower than t2? (or equal)"
  [t1 t2]
  (= t1 (combine-types t1 t2)))

(def widening-rules
;negation/tuples/indexed could be automatic from covariance annotation.? (maybe not-- special logic for tying dom->rng?)
  [(rule absorption
         [:- [t1] :+ [t2] :when (do (println "narrower: " t1 ", " t2) (narrower? t1 t2))])
   (rule range-simplification
         [:- [t1]
          :- [t2]
          :let [c1s (gather-matches [l u] t1 [:Range l u])]
          :let [c2s (gather-matches [l u] t2 [:Range l u])]
          :when (= 1 (count c1s))
          :when (= 1 (count c2s))
          :let [[m1 M1] (first c1s)]
          :let [[m2 M2] (first c2s)]
          :when (and (<= m1 (inc M2))
                     (>= M1 m2))]
         [[{:Range {(min m1 m2) #{(max M1 M2)}}}]])
   (rule nested-union-unwrapping
         [:- [t1]
          :let [c1s (gather-matches tss t1 [:Union tss])]
          :when (= 1 (count c1s))
          :let [ts (first c1s)]]
         (map vector ts))
   (rule java-type-widening
         [:- [t1]
          :- [t2]
          :let [c1s (gather-matches c t1 [:OfClass c])]
          :let [c2s (gather-matches c t2 [:OfClass c])]
          :when (= 1 (count c1s))
          :when (= 1 (count c2s))
          :when (.isAssignableFrom (first c1s) (first c2s))]
         [[{:OfClass #{(first c1s)}}]])])

#_(awake widening-rules [ [{:Range {4 #{7}}}] [{:Range {0 #{4}}}] ])
#_(awake [(rule r [:- [:Hey a]
                 :let [bigger (inc a)
                       evenbigger (inc bigger)]
                 :when (do (println "calling" evenbigger) (even? evenbigger))]
              [[:Ho bigger]])] [[:Hey 3] [:Hey 4] [:Hey 5]])
#_(awake widening-rules [ [{:Range {4 #{7}}}] [{:Union #{#{{:Range {0 #{4}}} {:Range {7 #{10}}}}}} ] ])

;cooperation between Union and Negation
#_(awake narrowing-rules [[:Not #{{:Range {3 #{8}}}}]
                        [:Not #{{:Range {5 #{20}}}}]
                        [:Not #{{:Union #{#{{:Range {20 #{50}}}
                                            {:Range {0 #{3}}}}}}}]])


(declare ^:dynamic *var-level-rules*)
(declare impose-rules)

(def ^:dynamic *branch-depth* 0)
(def ^:dynamic *branch-depth-limit* 2)
;if a body of a guard has a serious error (but the guard is okay) we must negate the guard (or ensure one of the earlier guards wins?)
;only triggered when creating the branch or a variable that is discussed in the branch is touched...
(defn dissoc-in
  [m [k & ks]]
  (if ks
    (assoc m k (dissoc-in (get m k) ks))
    (dissoc m k)))

(defn branch-guard
  [store branch-id arm]
  (if (>= *branch-depth* *branch-depth-limit*)
    false
    (binding [*branch-depth* (inc *branch-depth*)]
      (let [{:keys [guard body]} arm
            existing-errors (into #{} (errors store))
            store-sans-branch (dissoc-in store [:branch branch-id])
            guarded-store (awake *var-level-rules* store-sans-branch (unwrap guard))
            _ (trace [:branch-guard] [*branch-depth* "store sans branch is: " store-sans-branch])
            _ (trace [:branch-guard] [*branch-depth* "guarded store: " guarded-store])
            new-errors (set/difference (into #{} (errors guarded-store))
                                       existing-errors)
            _ (trace [:branch-guard] [*branch-depth* "new errors:" new-errors])]
        (not-empty new-errors)))))


;TODO: if we know an "is" is true on a body (i.e. due to an if- guard), then we can assert the guards as true. (same for false).
;      if body violates 'musts', then we negate the guard as a must. (this would be hard.. how to negate a relation? How to negate multiple asserions? Not easy to do it nicely.)
(defn branch-body
  [store id arm]
  (let [other-branches (gather-matches a store [:branch id a])]
    (trace [:branch-body] ["others:" other-branches " on store " store])
    (case (count other-branches)
      0 [[:Error id (str "Can't satisfy any of the branch guards on branch " id)]
         [:delete-branch-id! id]]
      1 (let [o-arm (first other-branches)]
          (trace [:branch-body] ["I'm going to unwrap " (unwrap (:body o-arm))])
          (concat [[:delete-branch-id! id]]
                  (map (fn [[funct is t]] [:must is t]) (unwrap (:guard o-arm)))
                  (unwrap (:body o-arm))))
      [])))

(def impose-rules
  [(rule delete-branch-id ;TODO not delving into nested branch stores yet. Can't probably do that w/o builtiness.
         [:+ [:delete-branch-id! id]
          :- [:branch id arm]]
         [])
   (rule remove-references
         [:+ [:delete-branch-id! id]
          :- [:branched-by x id]]
         [])
   #_(rule impossible-guard
           [:- [:branch id arm]
            :store store
            :when (branch-guard store id arm)]
           (branch-body store id arm))
   (rule wake-branch
         [:+ [:branched-by x id]
          :+ [:is x t]
          :- [:branch id arm]
          :store store
          :when (branch-guard (impose-constraint store [:is x t]) id arm)]
         (branch-body store id arm))
   (rule resolve-musts
         [:- [:must x t1]
          :- [:must x t2]
          :when (store? t1)
          :when (store? t2)]
         [[:must x (combine-types t1 t2)]])
   (rule resolve-is
         [:- [:is x t1]
          :- [:is x t2]
          :when (store? t1)
          :when (store? t2)]
         [[:is x (combine-types t1 t2)]])])

(defn min-mode
  "calculates the most conservative modality.
   [[:Is :Is]   :Is] -> :Is
   [[:Is :Must] :Is] -> :Must"
  [& modes]
  (if (every? #{:is} modes)
    :is
    :must))

(defrecord LocVar [id])
(defrecord BranchId [id])

(defmethod simple-dispatch LocVar
  [lv] (print (str "'" (or (:name (meta lv)) (:id lv)) "-" (:id lv))))
(defmethod simple-dispatch BranchId
  [lv] (print (str "'B" (or (:name (meta lv)) (:id lv)))))

(defn locvar
  ([gu-prefix id]
     (LocVar. (str gu-prefix id)))
  ([gu-prefix id name]
     (with-meta (locvar gu-prefix id) {:name name})))

(defn locvar? [o] (instance? LocVar o))

;48-57, 65-90, 97-122, //52 characters
(defn gu-range
  "returns an infinite sequence of unique prefixes-- optionally prepended with an already unique prefix"
  [& [gu-prefix]]
  (lazy-seq (concat (map (fn [i] (str gu-prefix (char i))) (concat (range 48 58) (range 65 91) (range 97 122)))
                    (gu-range (str gu-prefix "z")))))

;;TODO locals should claim a prefix so I know what to give other vars...
(defmacro locals
  "introduce a number of LocVars for a scope you own
   (so no globally-unique prefix appended to the ids)
   use like 'fresh'"
  [locvars & forms]
  `(let [~@(mapcat
            (fn [lv idx] [lv `(locvar "" ~idx (str (quote ~lv)))])
            locvars
            (gu-range))]
     ~@forms))

(defn assert-path [gu-prefix path-key nonlocal-set & args] 
  (let [{vars true consts false} (group-by locvar? args)
        locvars (map #(locvar %1 nil (str "const" %2)) (take (count consts) (gu-range gu-prefix)) (range))
        lvarred-args (first (reduce (fn [[va co] a] (if (locvar? a)
                                                      [(conj va a) co]
                                                      [(conj va (first co)) (rest co)]))
                                    [[] locvars] args))]
    (vec (concat [(vec (concat [path-key] lvarred-args [nonlocal-set]))] ;;needs to be at end as I never want to index on the nonlocal-set
                 (map (fn [lvar lval] [:is lvar lval]) locvars consts)
                 (for [v (rest lvarred-args)] [:watched-by v (first lvarred-args)])))))

;;; TODO: is there clear cases where this is important? I.e. where deferring certain reductions would allow us to avoid a misguided Union simplification? (probably for pathed things... but wouldn't we solve possible paths before their usages? Maybe for optimistic branches that only can pick intelligently with usage-info later in the code?)
;;; TODO: This isn't safe yet-- just regular solve everything eagerly.
(defn safe-solve
  "will solve only positive, narrowing constraints.
   no negation-as-fail, union simplification, branch elimination;
   i.e. rules that may erase constraints that could be narrowed or satisfied via eg inference."
  [store constraints]
  (awake *var-level-rules* store constraints))

;;; TODO: do we need a safe version of this that doesn't use union simplifications?  (for simplifying value types?)
(defn safe-combine-constraints
  [& ts]
  (apply combine-type-constraints ts))

;;; TODO: path rules, when deffed- should be keyed by their symbol for redeffing simplifity + namespacing.
;;; TODO: should we just auto-bind an "on" if there is any mention of the args in the guards/bodes? (i.e. no need to write it explicitly if you're just binding on the arg values? maybe too magical.
;;; TODO: should we namespace the key? I should think so.
;;; TODO: my :on form is backwards from regular :let in that I'm putting the "source" of the information on the left instead of the right. (though if you think of it as an [:is lvar pattern] like the other rules it makes sense...)
(defmacro path-rules
  "Path in the sense of Typed-Racket, allows constraint information to flow
   between code variables eg: from coll to (first coll).

   methods of form (ret-lvar [ch-rule-bindings] ret-values)
   bindings are as 'rule', except an :on form is provided, which acts only on the
   variables that have been connected with the path. eg ':on [a [:Max M1]]'
   will only match on 'a's that have been connected to ret-var through the path.

   ret values are wrapped with proper modality,
   i.e. [a b c] -> [[:is ret a][:is ret b][:is ret c]]

   Correctly handles mixed logical modalities (i.e. weakening 'is' to 'must' when necessary)"
  [path-name args & methods]
  (let [path-name-key (keyword path-name)
        mode-vars (into {} (map (juxt identity #(symbol (str % "-mode"))) args))]
    (vec (for [[[ret-var bindings ret-val] idx] (map vector methods (range))]
           (let [op-pairs (partition 2 bindings)          
                 on-statements (filter identity (map (fn [[op occ]] (when (= op :on) occ)) op-pairs))
                 nonlocal-vars-lvar (gensym "nonlocal-vars")]
             `(rule ~(with-meta 
                       (symbol (str path-name "-" idx))
                       {:tabled true})
                    ~(vec (apply concat
                                 (concat
                                  (apply concat
                                         (for [[var pat] on-statements]
                                           , (concat (if (= var (first args))
                                                       []
                                                       [[:+ [:watched-by var (first args)]]])
                                                     [[:+ [(mode-vars var) var pat]]])))
                                  [[:+ (vec (concat [path-name-key] args [nonlocal-vars-lvar]))]]
                                  (for [mv (map #(mode-vars (first %)) on-statements)] [:when `(#{:is :must} ~mv)])
                                  (remove (fn [[op occ]] (= op :on)) op-pairs))))
                    (map (fn [val#] [(min-mode (if (~nonlocal-vars-lvar ~ret-var) :must :is)
                                               ~@(map #(mode-vars (first %)) on-statements))
                                     ~ret-var
                                     val#])
                         ~ret-val)))))))

(def p-indexed-get-rules
  (path-rules p-indexed-get [r c dom-key]
              (r [:on [c [:Indexed dom rng]]
                  :on [dom-key dk]
                  :when (not (incompatible? dom dk))]
                 [rng])
              (c [:on [r t]
                  :on [dom-key dk]]
                 [{:Indexed {dk #{t}}}])))

(def p-get-in-rules
  (path-rules p-get-in [r c keys]
              (r [:on [c t]
                  :on [keys ks]]
                 (gather-matches elem t (concat ks [elem])))
              (c [:on [r t]
                  :on [keys ks]]
                 (assoc-in {} ks #{t}))))


;The key is a raw, literal key, not a type-level key.
(def p-get-rules
  (path-rules p-get [r col key]
              (r [:on [col c]
                  :on [key k]]
                 (gather-matches elem c [k elem]))
              (col [:on [r rt]
                    :on [key k]]
                   [(hash-map k #{rt})])))

#_(let [c (LocVar. "y")
      r (LocVar. "r")]
  [(awake (concat impose-rules p-get-rules)
          (concat [[:is c {:Bob #{3}} ]]
                  (assert-path nil :p-get #{} r c :Bob)))
   (awake (concat impose-rules p-get-rules)
          (concat [[:is r :some-value ]]
                  (assert-path nil :p-get #{} r c :Bob)))])

(defn falsey?
  [t]
  (or (= #{false} (:Bool t))
      (contains? t :Nil)))

(def p-<-rules
  (path-rules p-< [r a b]
              (r [:on [a [:Max M1]]
                  :on [b [:Min m2]]
                  :when (< M1 m2)]
                 [{:Bool #{true}}])
              (r [:on [a [:Min m1]]
                  :on [b [:Max M2]]
                  :when (< M2 m1)]
                 [{:Bool #{false}}])
              (a [:on [r t]
                  :on [b [:Min m]]]
                 (if (falsey? t)
                   [{:Min #{m}}]
                   [] ))
              (a [:on [r t]
                  :on [b [:Max M]]]
                 (if (falsey? t)
                   []
                   [{:Max #{(dec M)}}]))
              (b [:on [r t]
                  :on [a [:Min m]]]
                 (if (falsey? t)
                   []
                   [{:Min #{(inc m)}}]))
              (b [:on [r t]
                  :on [a [:Max M]]]
                 (if (falsey? t)
                   [{:Max #{M}}]
                   []))))

;;;TODO: handle union over idx ranges--for now only match when I know the exact integer statically. When would this be needed? Vector subset I guess?
;;Note: only writes to the tup when it already exists (so it knows the size)
(def p-tup-nth-rules
  (path-rules p-tup-nth [elem tup idx]
              (elem [:on [tup [:Tuple elems]]
                     :on [idx n]
                     :when (and (:Min n)
                                (= (first (:Max n))
                                   (first (:Min n))))]
                    (let [idx-val (first (:Min n))]
											(if (and (<= 0 idx-val)
															 (< idx-val (count elems)))
												[(nth elems idx-val)]
												[{:Error (str "Index "idx-val" out of range for Tuple "tup)}])))
              (tup [:on [elem t]
                    :on [idx n]
                    :on [tup [:Tuple elems]] ;;TODO: test. Does this behave as I expect? Setting up but depending on an existing shell of a tup.
                    :when (and (:Min n)
                               (= (first (:Max n))
                                  (first (:Min n))))]
                   (let [idx-val (first (:Min n))]
										 (if (and (<= 0 idx-val)
															(< idx-val (count elems)))
											 [{:Tuple (assoc (vec (repeat (count elems) {})) idx-val t)}]
											 [{:Error (str "Index "idx-val" out of range for Tuple "tup)}])))))


#_(def p-tupled-rules
  [[(rule fwd
          [:+ [:watched-by e r]
           :+ [:p-tupled r es nonlocals]
           :when (some #{e} es)
           :+ [mv e t]
           :when (#{:is :must} mv)]
          [[(min-mode ) r {:Tuple ...}]])]])

#_(let [r (LocVar. 'r)]
    [(get (:is (awake (concat impose-rules p-<-rules)
                 (assert-path nil :p-< #{} r {:Min #{0} :Max #{5}}  {:Min #{6} :Max #{7}}))) r)
   (get (:is (awake (concat impose-rules p-<-rules)
                    (assert-path nil :p-< #{} r {:Min #{0} :Max #{5}}  {:Min #{-2} :Max #{-1}}))) r)
   (get (:is (awake (concat impose-rules p-<-rules)
                    (assert-path nil :p-< #{} {:Bool #{true}} r  {:Min #{-2} :Max #{-1}}))) r)])

;;FIXME: this is injecting CHR logical variables into the types. (or someone ahead of us.) namely positive-t.
;it's p-negate-1's fault.
; the subs look right, it's maybe not looking up the subs properly
(def p-negate-rules
  (path-rules p-negate [r a]
              (r [:on [a t]
                  :let [positive-t (if (store? t) (dissoc t :Not) nil)]   ;;TODO: we have to be careful, if we ever have a raw value in the types, the let could fire even if we don't match the rule. We can't guard before lets either.
                  :when (not-empty positive-t)]
                 [{:Not #{positive-t}}])
              (a [:on [r t]
                  :let [positive-t (if (store? t) (dissoc t :Not) nil)]
                  :when (not-empty positive-t)]
                 [{:Not #{positive-t}}])))

(def p-=-rules
  (path-rules p-= [r a]
              (r [:on [a t]]
                 [t])
              (a [:on [r t]]
                 [t])))

#_(let [r (LocVar. 'r)]
  [(get (:is (awake (concat impose-rules p-negate-rules)
                    (assert-path nil :p-negate #{} {:Bob #{0}} r ))) r)])

(def ^:dynamic *var-level-rules*
  (concat impose-rules
          p-indexed-get-rules
          p-get-rules
          p-get-in-rules
          p-negate-rules 
          p-=-rules
          p-<-rules))



#_(fresh [x y] (find-matches-recursive (store-values (awake impose-rules [[:is 'a {:Range {2 #{7}}} ]
                     [:is 'a {:Range {0 #{3}}} ]
                     [:branch 0 {:guard {:is {'a #{{:Range {4 #{7}}}}}}
                                  :body ()}]
                     [:branched-by 'a 0]])) [] [:Range x y]))
;({y 7, x 4} {y 3, x 2})
  
#_(unwrap (awake narrowing-rules [[:Tuple [{:Tuple #{[{:Range {0 #{4}}}]}} {:Range {1 #{6}}}]]
                                  [:Tuple [{:Tuple #{[{:Range {1 #{7}}}]}} {:Range {10 #{95}}}]] ] ))

#_(unwrap (awake narrowing-rules {:Range {1 #{6}}} [[:Range 7 8]]))

#_(awake impose-rules [[:is 'a {:Range {2 #{7}}} ] [:is 'a {:Range {0 #{3}}} ]])

;single branch failure
#_(awake impose-rules [[:is 'a {:Range {2 #{7}}} ]
                     [:is 'a {:Range {0 #{3}}} ]
                     [:branch 0 {:guard {:is {'a #{{:Range {4 #{7}}}}}}
                                  :body ()}]
                     [:branched-by 'a 0]])

;collapse to the only possible branch.
;TODO: batch semantics would be useful here, because if the first one fails we don't know a second one is coming yet. (we can never know how to put the successful one first)
;      --not necessary though, the :branched-by acts as a catalyst to do the reductions-- it's the closing paren so we won't prematurely kill the group until that clause is there. (we won't ever have branches opened up again so that's fine.)
#_(awake impose-rules [[:is 'a {:Range {2 #{7}}} ]
                     [:is 'a {:Range {0 #{4}}} ]
                     [:branch 0 {:guard {:is {'a #{{:Range {5 #{7}}}}}}
                                 :body {:is {'b #{{:Nope #{nil}}}}}}]
                     [:branch 0 {:guard {:is {'a #{{:Range {3 #{7}}}}}}
                                 :body {:is {'b #{{:Yes #{nil}}}}}}]
                     [:branched-by 'a 0]])


;just an example of duplicating constraints as they come in.
#_(awake [(rule hey [:+ [:something a] :store store :when (do (println "store is" store) true) ] [[:another a] ])] [ [:something 4] [:something 5] [:something 6] ])


;for (group-pairs (map #(m/match [%] [ [:+ a]] [:added a]) [[:+ 'dogs] ]))



(defn collect-instances
  [store class]
  (cond
   (instance? class store) #{store}
   (set? store) (apply set/union (map #(collect-instances % class) store))
   (map? store) (apply set/union (map (fn [[k v]] (set/union
                                                   (collect-instances k class)
                                                   (collect-instances v class)))
                                      store))
   (coll? store) (apply set/union (map #(collect-instances % class) store))
   :else #{}))



(defn rewrite-store
  "rewrite map overrides standard scope offsetting
   (which is an namespacing-ish approach to prevent name clashes.)"
  [store rewrite-map gu-prefix]
  (cond
   (contains? rewrite-map store) (get rewrite-map store)
   (instance? LocVar store) (update-in store [:id] (fn [id] (str gu-prefix id)))
   (instance? BranchId store) (update-in store [:id] (fn [id] (str gu-prefix id)))
   (set? store) (set (map #(rewrite-store % rewrite-map gu-prefix) store))
   (map? store) (into {} (map (fn [[k v]] [(rewrite-store k rewrite-map gu-prefix)
                                           (rewrite-store v rewrite-map gu-prefix)])
                              store))
   (coll? store) (into (empty store) (map #(rewrite-store % rewrite-map gu-prefix) store))
   :else store))

;not sure if I should have separate guid counters for vars and branches or not. It allows all same-scoped vars to share a scope-id... seems to make a touch mores sense: it's like a composite key.
;TODO switch order for consistency with paths.
(defn apply-type-fn
  "returns a store rewritten so the rewrite-fn connects the args to the ret."
  [store gu-prefix args ret {fn-store :store fn-args :args fn-ret :ret}]
  (let [fn-store (rewrite-store fn-store
                                (into {} (map vector (conj fn-args fn-ret) (conj args ret) ))
                                gu-prefix)]
    (trace [:apply-type-fn] ["old-store" store])
    (trace [:apply-type-fn] ["fn-store" (unwrap fn-store)])
    (awake *var-level-rules*
           store (unwrap fn-store))))


;---- checking that we don't have name collisions, the type fns are applied to the right guy.
#_(def some-t-fn
  (locals [a]
    {:store {:is {a #{{:Min #{5}}}}}
     :args []
     :ret a}))

;rightly argues that b has a conflict.
#_(let [a (LocVar. "a")
        b (LocVar. "b")]
    (apply-type-fn {:is {a #{{:Max #{4}}}
                         b #{{:Max #{4}}}}}
                 nil [] b some-t-fn))

(def ^:dynamic *gu-prefix-counter* (fn [] (throw (Exception. "Tried to create a locvar w/o a gu-prefix-counter in dynamic scope"))))
(defn mk-gu-prefix-generator [& [pfx]]
  (let [counter (atom (concat [[nil]] (gu-range pfx)))]
    (fn [] (first (swap! counter rest)))))

;;;TODO: use actual ns resolution
(def builtins
  {'cljs.user.nth
   , (locals [col 
              index
              r
              min-size-dec
              min-size]
             {:Rewrite-Fn
              #{{:args [col index]
                 :ret r
                 :store {:p-get {min-size {col #{:Min-Size}}
                                 min-size-dec {index #{:Min}}} #_[:p-get min-size :is col :must :Min-Size] ;modalities before or after? probably after is more performant because I always iterate over modalities... I could store modalities as a signature tuple. They'll never be looked-for specifically anyway. They'll always be a package. It would make sense for the sig to be first--- but I'm not sure I would want to iterate over them so I guess they'll be after all logical vars? Again---polyvarity kind of hates this but... Maybe just metadata-- the exception would be owned or unowned? --no that's kind of hidden. The metadata would leak into the vars asserted. We'd also lose it on serialization unless we were careful.
                         :p-inc {min-size #{min-size-dec}} #_[:p-inc :is min-size :is min-size-dec]
                         #_[:p-get :is min-size-dec :must index :Min] ;<-- for some reason this should be a weakening relation... If I know min size is so and so, I wan't to say index Must be bigger... not IS bigger... Why?? because it's not in a guard here.
                         :watched-by {col #{min-size}
                                      min-size-dec #{min-size}
                                      index #{min-size-dec}}
                         :must {index #{{:Min 0}}
                                col :??}}}}})
   'cljs.user.instance_QMARK_ ;; TODO: we don't complain if class is not an actual class.
   (locals [class c ct x r]
           (let [pc (mk-gu-prefix-generator 5)
                 b-id (BranchId. (pc))]
             {:Rewrite-Fn
              , #{{:args [class x]
                   :ret r
                   :store (awake
                           []
                           {:branch {b-id
                                     #{{:guard (awake [] (assert-path (pc) :p-get #{} c x :OfClass))                                       
                                        :body {:is {r {:Bool #{true}}}}}
                                       {:guard (awake [] (concat (assert-path (pc) :p-get #{} c ct :OfClass)
                                                                 (assert-path (pc) :p-negate #{} x ct)))
                                        :body {:is {r {:Bool #{false}}}}}}}
                            :branched-by {r #{b-id} ;;TODO: auto infer these? Because ct is local to the guard and doesn't escape? Have a branch that can introduce it's own locals, any non-locals are free and linked to the branch?
                                          x #{b-id}
                                          c #{b-id}}}
                           (assert-path (pc) :p-get #{} c class :Class))}}}))})

(defn deduce
  "THIS IS IN FLUX -- but is intended to execute the deductive process,
   parsing analyzed forms, inferring constraints, and firing applicable rules."
  [store env analysis gu-prefix & [ret-locvar]]
  (let [path-typed? (fn path-typed? [r] (locvar? r))
        [gu-prefix ret-locvar] (if ret-locvar
                                 [gu-prefix ret-locvar]
                                 [(str gu-prefix "1") (locvar gu-prefix 0 "ret")])]
    (case (:op analysis)
      :literal-type ;a type sitting in the actual source analysis-- possibly written in by analysis->analysis transformations.
        [store (:type analysis)]
    
      :constant ;------------------------------------------------------------------------
        (condp = (type (:form analysis))
            java.lang.Long [store {:Min #{(:form analysis)} :Max #{(:form analysis)}
                                   :OfClass #{java.lang.Long}}]
            clojure.lang.Keyword [store {:Keyword #{(:form analysis)}
                                         :OfClass #{clojure.lang.Keyword}}]
            java.lang.Boolean [store {:Bool #{(:form analysis)}
                                      :OfClass #{java.lang.Boolean}}]
            clojure.lang.Symbol [store {:Symbol #{(keyword (:form analysis))}
                                        :OfClass #{clojure.lang.Symbol}}]
            [store {:OfClass #{(type (:form analysis))}}])
    
      :var ;------------------------------------------------------------------------
        (if-let [t (get builtins (:name (:info analysis)))]
          [store t]
          (if (re-find #"\." (str (resolve (:form analysis))))
            [store {:Class #{(resolve (:form analysis))} :OfClass #{java.lang.Class}}] ;not seen as a constant by js analyzer
            [store, (env (:name (:info analysis)))])) ;; TODO: used to be {:relation [r-equals (:name (:info analysis))]}-- should look this up in the environment-- 
    
      :map ;------------------------------------------------------------------------
        (let [[s idxs] (reduce (fn [[s,idxs],[k v guid]]
                                 (let [[s1 kt] (deduce s env k (str guid 0))
                                       [s2 vt] (deduce s1 env v (str guid 1))]
                                   [s2 (conj idxs [kt vt])]))
                               [store, []]
                               (map vector (:keys analysis) (:vals analysis) (gu-range gu-prefix)))]
          (if (some (fn [[kt vt]] (or (path-typed? kt) (path-typed? vt))) idxs) 
            [(safe-solve s (concat
                            (for [[kt vt] idxs]
                              (if (path-typed? kt)
                                [[:is ret-locvar [:Error (str "Can't have path-typed-var " kt " as keys in a map literal at the moment")]]]
                                (assert-path :p-indexed-get #{} vt ret-locvar kt)))
                            [[:is ret-locvar [:OfClass clojure.lang.PersistentArrayMap]]])) 
             , ret-locvar]
            [s, (apply safe-combine-constraints
                       (concat (apply concat (for [[kt vt] idxs] [[:Indexed kt vt]]))
                               [[:OfClass clojure.lang.PersistentArrayMap]]))]))

      :vector ;------------------------------------------------------------------------
        (let [[s ts] (reduce (fn [[s ts] [elem guid]]
                               (let [[st0 t] (deduce s env elem guid)]
                                 [st0, (conj ts t)]))
                             [store, []]
                             (map vector (:children analysis) (gu-range gu-prefix)))
              sz (count ts)]
          (if (some path-typed? ts) 
            [(safe-solve s (concat (for [[t idx] (map vector ts (range))]
                                     (assert-path :p-tup-nth #{} t ret-locvar {:Min idx :Max idx} sz))
                                   [[:is ret-locvar [:OfClass clojure.lang.PersistentVector]]])) 
             , ret-locvar]
            [s {:Tuple #{ts}
                :OfClass #{clojure.lang.PersistentVector}}]))

      :let ;------------------------------------------------------------------------
        (let [[st0 env0] (reduce (fn [[s e] [bind guid]]
                                   (let [lv (locvar guid 0 (:name bind)) ;;TODO fix all to be guids
                                         e0 (trace [:deduce] ["env to: "(assoc e (:name bind) lv)])
                                         [s0 t] (deduce s e0 (:init bind) (str guid 1) lv)]
                                     #_"don't bother asserting that a var is equal to itself. We assume that's done."
                                     (if (path-typed? t)
                                       [s0 e0]
                                       [(safe-solve s0 [[:is lv t]]) e0])))
                                 [store env]
                                 (map vector (:bindings analysis) (gu-range gu-prefix)))
              st1 (reduce (fn [s statement] (first (deduce s env0 statement))) ;;TODO: collect any ill-typed value-types here. They wouldn't be captured or propagate to anyone else o/w but surely we'd want to know about them.
                          st0
                          (:statements analysis))]
          (deduce st1 env0 (:ret analysis) ret-locvar))
    
      :new ;TODO, check against constructor requirements: (for [c (.getConstructors Integer) arg (.getParameterTypes c) ] arg )
        [store {:OfClass #{(get-in analysis [:ctor :form])}}]

;    :dot ;only works if we can resolve type... a future maybe.
;      :???-java-invocation-via-reflection?
    
      :invoke ;------------------------------------------------------------------------
        (let [[s0 f-type] (deduce store env (:f analysis) (str gu-prefix 0))
;args (map fresh (repeat (count (:args analysis)) "arg"))            
              [s0 arg-types]
              , (reduce (fn [[s ats] [arg-an guid arg-idx]] ;<- bind "is" info to f and args temp variables.
                          (let [[st-next ty] (deduce s env arg-an (str guid 0))
                                [st-next0 ty0] (if (locvar? ty)
                                                 [st-next ty]
                                                 (let [argvar (locvar guid 1 (str "arg" arg-idx))]
                                                   [(safe-solve st-next [[:is argvar ty]]) argvar]))]
                            [st-next0 (conj ats ty0)])) 
                        [store []]
                        (map vector (:args analysis) (gu-range (str gu-prefix 1)) (range)))
              _ (trace [:deduces] ["invoke" s0 f-type arg-types ret-locvar]) ]
          (if (= 1 (count (:Rewrite-Fn f-type)))
            [(apply-type-fn s0 (str gu-prefix 2) arg-types ret-locvar (first (:Rewrite-Fn f-type))) ret-locvar]
            [s0 {:Error #{(str "cannot apply " f-type " as a :Rewrite-Fn")}}]))
    
      :fn ;------------------------------------------------------------------------
        nil #_(let [compact-&-errs
                    , (for [method (:methods analysis)]
                        (let [[s0 _t-statements] (if-let [sm (:statements method)]
                                                   (deduce store sm)
                                                   [store nil])
                              [s1 t-ret] (deduce s0 (:ret method) ret)
                              errs (new-errors store s1)
                              _ (trace [:deduce] ["fn typing s0" s0 "s1" s1 "t-ret" t-ret ""])
                              compact-store (filter-store s1 (into #{} (concat (:params method) (collect-lvars t-ret))))
                              _ (trace [:deduce] ["compacted store" compact-store])]
                          [{:params (:params method)
                            :ret t-ret
                            :store compact-store
                            :variadic (:variadic method)}, errs]))
                    total-errs (into #{} (mapcat second compact-&-errs))
                    final-store (if (empty? total-errs)
                                  store
                                  (assoc-in store [:errors (fresh (:name analysis))] total-errs))]
                [final-store
                 (if true #_"TODO: assume all are complicated for now"
                     {:type-fn (vec (map first compact-&-errs))}
                     {:Fn #{{:indices (into #{} ::??dom->rngs??)
                             :polyvarity (inc (:max-fixed-arity analysis))}}})])
    
      :if ;------------------------------------------------------------------------ 
        nil #_(let [[s0 t-test] (deduce store (:test analysis))
                    [test-var s1] (if-let [tv (get-r-equals t-test)]
                                    [tv s0]
                                    (let [tv (fresh "test-")]
                                      [tv (assert-constraint s0 (is tv t-test))]))
                    ret-var (or ret-locvar (fresh "ifret-"))
                    [s-then-0 t-then] (deduce (fresh-fork-store s1) (:then analysis))
                    s-then-1 (assert-constraint s-then-0 (is ret-var t-then))
                    _ (trace [:deduces :infer-if] ["then-branch:" s-then-1])
                    [s-else-0 t-else] (deduce (fresh-fork-store s-then-1) (:else analysis))
                    s-else-1 (assert-constraint s-else-0 (is ret-var t-else))
                    _ (trace [:deduces :infer-if] ["else-branch:" s-else-1])
                    s2 (assert-constraint s1 [:Branch [{:guard {test-var {:Is {:Not #{{:Nil #{nil}}
                                                                                      {:Bool #{false}}}}}}
                                                        :body s-then-1}
                                                       {:guard {test-var {:Is {:Union #{#{{:Nil #{nil}}
                                                                                          {:Bool #{false}}}}}}}
                                                        :body s-else-1}]])] 
                [s2 {:relation [r-equals ret-var]}]) ;{:branch-assigned #{[(dec (:next-branch-id s2)) ret-var]}}
      #_"unknown op"
      [store {}])))

#_(defmacro check [form]
  `(deduce {} {} (comp/analyze nil (quote ~form)) nil))


;;FIXME: trying to make a range [53, 4] out of this.
#_(check {"dog" 4 "cat" 53})


;OK-- works on agreement and disagreement.
#_(let [klass (LocVar. 0 "klass")
      item (LocVar. 0 "item")
      ret (LocVar. 0 "ret")] ;FIXME: We don't know what scope ret should be here! It depends on the scope of the apply-type-fn which "owns" ret...
    (apply-type-fn {:is {item #{{:OfClass #{String}}}
                         klass #{{:Class #{Number}}}}}
                   [klass item] ret (get builtins 'cljs.core.instance_QMARK_)))

;rightly complains
#_(combine-types {:Not #{{:OfClass #{java.lang.Number}}},} {:OfClass #{java.lang.Number}})

;works again.
#_(awake *var-level-rules* [[:is :a {:Dog #{3}}]
                            [:is :a {:Not #{{:Dog #{3}}}}]])

;should complain.
#_(combine-types {:Not #{#{{:Dog #{3}}}}} {:Dog #{3}})

;rightly complains
#_(awake *var-level-rules* [[:is :a {:Min #{0} :Max #{10}}]
                            [:is :a {:Not #{{:Min #{5} :Max #{15}}}}]])

;non overlaps should be OK... no way of ensure we reduce both min + max before checking Nil... Need rule priorities or aggregates now for sure. kind of different--we want all negation constraints to be deferred to last possible moment. (not just the rules to be considered 'last')... That's a constraint-level priority, not a rule-level priority. (i.e the active constraint should be suspended if it's a :Not, and there are non-:Not's on the queue)...
#_(awake *var-level-rules* [[:is :a {:Min #{16} :Max #{20}}]
                            [:is :a {:Not #{{:Min #{7} :Max #{15}}}}]])

;complain on overlaps
#_(awake *var-level-rules* [[:is :a {:Min #{10} :Max #{20}}]
                          [:is :a {:Not #{{:Min #{7} :Max #{15}}}}]])


;this rightly returns false... ?
#_(overlap? {:Min #{7} :Max #{15}} {:Min #{16} :Max #{20}} )

;rightly complains about the incongruence through "c"
#_(awake (concat impose-rules p-get-rules) {}
       (concat
        [[:is (LocVar. "class") {:Class #{Number}}]
         [:is (LocVar. "item") {:OfClass #{String}}]]
        (assert-path 0 :p-get #{} (LocVar. "c") (LocVar. "item") :OfClass)
        (assert-path 1 :p-get #{} (LocVar. "c") (LocVar. "class") :Class)))