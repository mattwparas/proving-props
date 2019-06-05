#lang racket

(provide trie)
(provide empty-trie)

;; --------------------- CONTRACTS -------------------- ;;

(provide 
 (contract-out
  [lookup-helper (-> trie? (non-empty-listof char?) boolean?)]
  [lookup (-> trie? string? boolean?)]
  ;; TODO maybe use nat instead of integer
  [create-children (-> (non-empty-listof char?) (listof trie?) (listof char?) (listof trie?))]
  [handle-last-letter (-> (listof char?) (listof trie?) (listof char?) (listof trie?))]
  [handle-intern-letter (-> (listof char?) (listof trie?) (listof char?) (listof trie?))]
[insert (->i ([x trie?] 
              [y string?])
             [res (and/c trie? (lambda (res) all-children-in-order res))])]
  [trie<? (-> trie? trie? boolean?)]
  [pre-order-traverse (-> trie? void)]
[build-trie-from-list-of-words
 (->i ([x trie?]
       [y (and/c (listof string?) (lambda (y)
                                    (only-unique-words y)))])
      [res (y) (and/c trie? (and/c (lambda (res) all-children-in-order res)
                                   (and/c
                                    (lambda (res) (num-of-char-nodes<=num-of-chars res y))
                                    (lambda (res) (num-of-words=num-of-true res y)))))])]
  [trie-sort (->i ([y (listof string?)])
                  [res (y) (and/c (lambda (res) (ordered-strings? res))
                                  (and/c (lambda (res) (permutation? y res))
                                         (listof string?)))])]
  [pre-order (-> trie? (listof integer?))]
  ))

;; ------------------------- TRIE ---------------------------- ;;


(struct trie (char children end-word? word-up-to) #:transparent)

(define empty-trie (trie void empty #f empty))


;; contract: trie? (listof char?) -> bool?
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

;; contract: trie? string? -> bool?
(define (lookup root-trie word)
  (define char-list (string->list word))
  (if (not (empty? char-list)) ;; if not empty, perform search
      (for/first ([i (trie-children root-trie)]
                  #:when (char=? (first char-list) (trie-char i)))
        (lookup-helper i char-list))
      #f)) ;; otherwise return false

;; contract: (listof char?) (listof tries?) integer? -> (listof trie?)
(define (create-children char-list lst prefix-chars)
  (cond [(= (length char-list) 1)
         (handle-last-letter char-list lst prefix-chars)]
        [else ;; you are in the middle of the word
         (handle-intern-letter char-list lst prefix-chars)]))

;; contract: (listof char?) (listof trie?) integer? -> (listof trie?)
(define (handle-last-letter char-list lst prefix-chars)
  (define char (first char-list))
  (define next-prefix (append prefix-chars (list char)))
  (cond [(empty? lst) ;; children are empty, return list of empty children
         (list (trie char empty #t next-prefix))]
        [(char<? char (trie-char (first lst))) ;; less than, put it to the left
         (cons (trie char empty #t next-prefix) lst)]
        [(char=? char (trie-char (first lst))) ;; equal, step down a level
         (cons (trie char (trie-children (first lst)) #t next-prefix) (rest lst))]
        [else ;; move to the right
         (cons (first lst)
               (create-children char-list (rest lst) prefix-chars))]))

;; contract: (listof char?) (listof trie?) integer? -> (listof trie?)
(define (handle-intern-letter char-list lst prefix-chars)
  (define char (first char-list))
  (define next-prefix (append prefix-chars (list char)))
  (cond [(empty? lst) ;; no children, pop off front and step down
         (list (trie char (create-children 
                           (rest char-list) empty next-prefix) #f next-prefix))]
        [(char<? char (trie-char (first lst))) ;; place where it is, pop off front and go
         (cons (trie char (create-children 
                           (rest char-list) empty next-prefix) #f next-prefix) lst)]
        [(char=? char (trie-char (first lst))) ;; equal, step down
         (cons (trie char (create-children (rest char-list) (trie-children (first lst)) next-prefix)
                     (trie-end-word? (first lst))
                     (trie-word-up-to (first lst)))
               (rest lst))]
        [else ; move to the right
         (cons (first lst)
               (create-children char-list (rest lst) prefix-chars))]))

;; contract: trie? string? integer? -> trie?
(define (insert root-trie word)
  (define char-list (string->list word))
  (trie
   (trie-char root-trie)
   (create-children char-list (trie-children root-trie) empty)
   (trie-end-word? root-trie)
   (trie-word-up-to root-trie)))

; contract: trie? trie? -> boolean?
(define (trie<? trie-node1 trie-node2)
  (char<? (trie-char trie-node1) (trie-char trie-node2)))

;; contract: trie? -> void
(define (pre-order-traverse trie-node)
  (displayln (list (trie-char trie-node) (trie-end-word? trie-node) (trie-word-up-to trie-node)))
  (map pre-order-traverse (trie-children trie-node))
  "finished")

;; contract: trie? (listof string?) -> trie?
(define (build-trie-from-list-of-words trie list-of-words)
  (cond
    [(= (length list-of-words) 1)
     (insert trie (first list-of-words))]
    [else
     (build-trie-from-list-of-words
      (insert trie (first list-of-words))
      (rest list-of-words))]))

;; ------------------ SORTING ---------------------- ;;

(define (trie-sort list-of-words)
  (define new-trie (build-trie-from-list-of-words empty-trie list-of-words))
  (pre-order new-trie))

; THIS ONE WORKS (using con and flatten)
;; contract: trie? -> (listof string?)
(define (pre-order trie-node)
  (if (trie-end-word? trie-node)
    (cons (list->string (trie-word-up-to trie-node))
      (flatten (map pre-order (trie-children trie-node))))
    (flatten (map pre-order (trie-children trie-node)))))

;; THIS ALSO WORKS (using foldr and map)
;; contract: trie? -> (listof string?)
;;; (define (pre-order trie-node)
;;;   (if (trie-end-word? trie-node)
;;;       (foldr append (list (list->string (trie-word-up-to trie-node)))
;;;              (map pre-order (trie-children trie-node)))
;;;       (foldr append empty (map pre-order (trie-children trie-node)))))

;; a little print test
(define test-list (list "apple" "app" "ape" "nest"))
(define trie1 (build-trie-from-list-of-words empty-trie test-list))
; (pre-order-traverse trie1)
; (displayln (pre-order trie1))

;; --------------------------- PROPERTY FUNCTIONS ------------------------------ ;;

;; used
;; contract: (listof string?) -> boolean?
(define (only-unique-words list-of-words) 
  (eq? (length (remove-duplicates list-of-words)) (length list-of-words)))

;; used
;; contract: trie? -> (listof string?)
(define (num-of-words=num-of-true trie-node list-of-words)
  (eq? (count-words-in-trie trie-node) (length list-of-words)))

;; contract: trie? -> (listof bool?)
(define (count-helper trie-node)
  (cons (trie-end-word? trie-node)
        (map count-helper (trie-children trie-node))))

;; contract: trie? -> natural?
(define (count-words-in-trie trie-node)
  (define t-and-f-list
    (filter (lambda (element) element)
            (flatten (count-helper trie-node))))
  (length t-and-f-list))

;; used
;; contract: trie? (listof string?) -> boolean?
(define (num-of-char-nodes<=num-of-chars trie-node list-of-words)
  (<= (count-char-nodes-in-trie trie-node) (num-of-chars list-of-words)))

;; contract: trie? -> (listof char?)
(define (count-char-nodes-helper trie-node)
  (cons (trie-char trie-node) 
        (map count-helper (trie-children trie-node))))

;; contract: trie? -> natural?
(define (count-char-nodes-in-trie trie-node)
  (- (length (count-char-nodes-helper trie-node)) 1))

;; contract: (listof string?) -> natural?
(define (num-of-chars list-of-words)
  (for/sum ([word list-of-words])
    (length (string->list word))))

;; contract: (listof char?) -> boolean?
(define (ordered? lst)
  (cond [(empty? lst) #t]
        [(= (length lst) 1) #t]
        [(char<? (first lst) (first (rest lst)))
         (ordered? (rest lst))]
        [else #f]))

;; contract: (listof string?) -> boolean?
(define (ordered-strings? lst)
  (cond [(empty? lst) #t]
        [(= (length lst) 1) #t]
        [(string<? (first lst) (first (rest lst)))
          (ordered-strings? (rest lst))]
        [else #f]))

(define (string-list-sorted? lst)
  (apply string<? lst))

;; contract: trie? -> boolean?
(define (child-in-order trie-node)
  (define children-chars 
    (map (lambda (child-node) 
           (trie-char child-node))))
  (ordered? children-chars))

;; contract: trie? -> boolean?
(define (all-children-in-order trie-node)
  (and (child-in-order trie-node)
       (for/and ([child (trie-children trie-node)])
         (all-children-in-order child))))

;; contract: (listof string?) (listof string?) -> boolean?
(define (permutation? list1 list2)
  (and
   (not (check-duplicates list1))
   (not (check-duplicates list2))
   (= (length list1) (length list2))
   (for/and ([i list1])
     (not (false? (member i list2))))
   (for/and ([i list2])
     (not (false? (member i list1))))))
