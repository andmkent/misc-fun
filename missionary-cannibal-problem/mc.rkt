#lang racket

;; written by Andrew M. Kent 2015

(require redex)
;; Missionary-Cannibal (MC) language
;; A grammar to define the problem space for the
;; missionaries and cannibals problem (Amarel, 1968)
(define-language MC
  ;; missionary
  [M ::= m]
  ;; cannibal
  [C ::= c]
  ;; missionary or cannibal
  [P ::= M C]
  ;; there are only two shores
  [Shore ::= start end]
  ;; starting shore
  [Start ::= (start M ... C ...)]
  ;; boat (size constraint enforced by 'safe-place' relation)
  [Boat ::= (boat M ... C ...)]
  ;; target shore
  [End ::= (end M ... C ...)]
  ;; a location is either shore or the boat
  [Loc ::= Start Boat End]
  ;; the state includes the two shores, the boat, and the river
  ;; (the river is either at one shore or another in this state)
  [State ::= (Start Boat river End) (Start river Boat End)])

;; we begin w/ 3 missionaries and cannibals
;; at the start shore and an empty boat
(define initial-state
  (term [(start m m m c c c) (boat) river (end)]))

(define-judgment-form MC
  #:mode (safe-place I) #:contract (safe-place Loc)
  ;; a shore is safe if there are no missionaries
  ;; *or* if the number of missionaries >= the number of cannibals
  [(where #t ,(or (empty? (term (M ...)))
                  (>= (length (term (M ...)))
                      (length (term (C ...))))))
   ------------- "Safe-Start"
   (safe-place (Shore M ... C ...))]
  
  ;; the boat is safe if the number of missionaries
  ;; and cannibals is <= 2
  [(where #t ,(<= (length (term (M ... C ...)))
                  2))
   ------------- "Safe-Boat"
   (safe-place (boat M ... C ...))])

;; add-to
;; helper function, just adds a series of Ps to a Shore or Boat
;; (any acts as a wild card)
(define-metafunction MC
  add-to : Loc P -> Loc
  [(add-to (any M ... C ...) M_new) (any M_new M ... C ...)]
  [(add-to (any M ... C ...) C_new) (any M ... C ... C_new)])


;; the 'move' relation
;; this is a subset of (State × State)
;; specifying which States a State can transition into
(define move
  (reduction-relation
   MC
   #:domain State
   ;; loading 1 Missionary onto the boat
   [[(start M M_s ... C_s ...) Boat river End]
    . --> .
    [(start M_s ... C_s ...) (add-to Boat M) river End]
    ;; if constraints are met:
    (judgment-holds (safe-place (start M_s ... C_s ...)))
    (judgment-holds (safe-place (add-to Boat M)))
    (judgment-holds (safe-place End))
    load-1M]

   ;; loading 1 Cannibal onto the boat
   [[(start M_s ... C C_s ...) Boat river End]
    . --> .
    [(start M_s ... C_s ...) (add-to Boat C) river End]
    ;; if constraints are met:
    (judgment-holds (safe-place (start M_s ... C_s ...)))
    (judgment-holds (safe-place (add-to Boat C)))
    (judgment-holds (safe-place End))
    load-1C]

   ;; moving the boat from the start to end Shore
   [[Start (boat P P_rst ...) river End]
    . --> .
    [Start river (boat P P_rst ...) End]
    ;; if constraints are met:
    (judgment-holds (safe-place Start))
    (judgment-holds (safe-place (boat P P_rst ...)))
    (judgment-holds (safe-place End))
    row-right]


   
   ;; unloading 1 Missionary
   [[Start river (boat M P ...) End]
    . --> .
    [Start river (boat P ...) (add-to End M)]
    ;; if constraints are met:
    (judgment-holds (safe-place Start))
    (judgment-holds (safe-place (boat P ...)))
    (judgment-holds (safe-place (add-to End M)))
    unload-1M]
   
   ;; unloading 1 Cannibal
   [[Start river (boat P ... C) End]
    . --> . 
    [Start river (boat P ...) (add-to End C)]
    ;; if constraints are met:
    (judgment-holds (safe-place Start))
    (judgment-holds (safe-place (boat P ...)))
    (judgment-holds (safe-place (add-to End C)))
    unload-1C]
   
   ;; moving the boat from the end to start Shore
   [[Start river (boat P P_rst ...) End]
    . --> . 
    [Start (boat P P_rst ...) river End]
    ;; if constraints are met:
    (judgment-holds (safe-place Start))
    (judgment-holds (safe-place (boat P P_rst ...)))
    (judgment-holds (safe-place End))
    row-back]))

;; 'traces' generates the space defined
;; by the transitive closure of the 'move' relation
;; beginning with the 'initial-state' we defined above
(traces move initial-state)
