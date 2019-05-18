#lang racket

(provide trie)
(provide empty-trie)

(provide 
  (contract-out
    [lookup-helper (-> trie? (non-empty-listof char?) boolean?)]
    [lookup (-> trie? string? boolean?)]
    ;; TODO maybe use nat instead of integer
    [create-children (-> (non-empty-listof char?) (listof trie?) integer? (listof trie?))]
    [handle-last-letter (-> (listof char?) (listof trie?) integer? (listof trie?))]
    [handle-intern-letter (-> (listof char?) (listof trie?) integer? (listof trie?))]
    [insert (-> trie? string? integer? trie?)]
    [trie<? (-> trie? trie? boolean?)]
    [pre-order-traverse (-> trie? void)]
    [build-trie-from-list-of-words (-> trie? (listof string?) integer? trie?)]
    [not-neg-one (-> integer? boolean?)]
    [trie-sort (-> trie? (listof string?) (listof string?))]
    [pre-order-helper (-> trie? (listof integer?))]
))

;; char       :   character
;; children   :   list-of-tries
;; end-word?  :  bool
;; index      :  int        (index of word in the original list)
(struct trie (char children end-word? index) #:transparent)

;; contract: trie list-of-characters -> bool
(define (lookup-helper trie-node char-list)
  (cond
  [(empty? char-list) #f] ; hit the case where its empty THIS IS PROBABLY NOT NEEDED
  [(not (char=? (first char-list) (trie-char trie-node))) #f] ; no match, false
  [(= (length char-list) 1) ; return if its an end word
    (trie-end-word? trie-node)] ; #t or #f here
  [else
    (for/first ([i (trie-children trie-node)]
      #:when (char=? (first (rest char-list)) (trie-char i)))
      (lookup-helper i (rest char-list)))])) ; recur on the child which matches character

;; contract: trie string -> bool
(define (lookup root-trie word)
  (define char-list (string->list word))
  (if (not (empty? char-list)) ;; if not empty, perform search
    (for/first ([i (trie-children root-trie)]
      #:when (char=? (first char-list) (trie-char i)))
      (lookup-helper i char-list))
    #f)) ;; otherwise return false

;; contract: list-of-chars list-of-tries int -> list-of-tries
(define (create-children char-list lst index)
  (cond [(= (length char-list) 1)
          (handle-last-letter char-list lst index)]
        [else ;; you are in the middle of the word
          (handle-intern-letter char-list lst index)]))

;; contract: list-of-chars list-of-tries int -> list-of-tries
(define (handle-last-letter char-list lst index)
  (define char (first char-list))
  (cond [(empty? lst) 
            (list (trie char empty #t index))]
        [(char<? char (trie-char (first lst)))
            (cons (trie char empty #t index) lst)]
        [(char=? char (trie-char (first lst)))
            (cons (trie char (trie-children (first lst)) #t index) (rest lst))]
        [else
            (cons (first lst)
                  (create-children char-list (rest lst) index))]))

;; contract: list-of-chars list-of-tries int -> list-of-tries
(define (handle-intern-letter char-list lst index)
  (define char (first char-list))
  (cond [(empty? lst)
          (list (trie char (create-children 
                              (rest char-list) empty index) #f -1))]
        [(char<? char (trie-char (first lst)))
            (cons (trie char (create-children 
                                (rest char-list) empty index) #f -1) lst)]
        [(char=? char (trie-char (first lst)))
            (cons (trie char (create-children
                                (rest char-list) (trie-children (first lst)) index) #f -1) (rest lst))]
        [else
            (cons (first lst)
                  (create-children char-list (rest lst) index))]))

;; contract: trie string integer -> trie
(define (insert root-trie word index)
  (define char-list (string->list word))
  (trie
    (trie-char root-trie)
      (create-children char-list (trie-children root-trie) index)
      (trie-end-word? root-trie)
      (trie-index root-trie)))

;; contract: trie trie -> bool
(define (trie<? trie1 trie2)
  (char<? (trie-char trie1) (trie-char trie2)))

;; contract: trie -> void
(define (pre-order-traverse trie-node)
  (displayln (list (trie-char trie-node) (trie-end-word? trie-node) (trie-index trie-node)))
  (map pre-order-traverse (trie-children trie-node))
  "finished")

;; contract: trie list-of-strings int -> trie
(define (build-trie-from-list-of-words trie list-of-words index)
  (cond
    [(= (length list-of-words) 1)
      (insert trie (first list-of-words) index)]
    [else
      (build-trie-from-list-of-words
        (insert trie (first list-of-words) index)
          (rest list-of-words) (+ 1 index))]))

;; contract: integer? -> boolean?
(define (not-neg-one num)
  (not (= -1 num)))

;; contract: trie listof-string? -> listof-string?
(define (trie-sort trie-node list-of-words)
  (define indices
    (filter not-neg-one
      (flatten (pre-order-helper trie-node))))
  (map (lambda (index) (list-ref list-of-words index)) indices))

;; contract: trie? -> listof-integer?
(define (pre-order-helper trie-node)
  (cons (trie-index trie-node)
  (map pre-order-helper (trie-children trie-node))))

;; contract: void -> trie
(define empty-trie (trie void empty #f -1))

