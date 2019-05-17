#lang racket

(require rackunit)
(require rackunit/text-ui)


;; char       :   character
;; children   :   list-of-tries
;;    assume the list of children is ordered? maybe?
;; end-word?  :  bool
;; index      :  int
;;    index of word in the original list
(struct trie (char children end-word? index) #:transparent)

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
))

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

;; contract: void -> trie
(define empty-trie (trie void empty #f -1))

;;;;;;;;;;;;;;;;;;;;;;;;; TESTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; words in this test trie
;; bad, bat, bam, bet, bed, bell
(define testtrie
  (trie ; define the root 
    void ; contains no character
      (list
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t -1)
                (trie #\m empty #t -1)
                (trie #\t empty #t -1)) 
              #f -1)
            (trie #\e 
              (list
                (trie #\d empty #t -1)
                (trie #\l (list (trie #\l empty #t -1)) #f -1)
                (trie #\t empty #t -1)) 
          #f -1)) 
      #f -1)) 
#f -1))

;;; words in this test trie
;; bad, bat, bam, bet, bed, bell
(define better-testtrie
  (trie ; define the root 
    void ; contains no character
      (list
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t 0)
                (trie #\m empty #t 2)
                (trie #\t empty #t 1)) 
              #f -1)
            (trie #\e 
              (list
                (trie #\d empty #t 4)
                (trie #\l (list (trie #\l empty #t 5)) #f -1)
                (trie #\t empty #t 3)) 
          #f -1)) 
      #f -1)) 
#f -1))

;; trie after inserting the word "app"
(define testtrie_after_insert
  (trie ; define the root 
    void ; contains no character
      (list
        (trie #\a
          (list 
            (trie #\p 
              (list 
                (trie #\p empty #t -1)) #f -1))
            #f -1)
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t -1)
                (trie #\m empty #t -1)
                (trie #\t empty #t -1))
              #f -1)
            (trie #\e 
              (list
                (trie #\d empty #t -1)
                (trie #\l (list (trie #\l empty #t -1)) #f -1)
                (trie #\t empty #t -1)) 
          #f -1)) 
      #f -1)) 
#f -1))

;;; words in this test trie
;; bad, bat, bam, bet, bed, bell
(define testtrie_after_insert_be
  (trie ; define the root 
    void ; contains no character
      (list
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t -1)
                (trie #\m empty #t -1)
                (trie #\t empty #t -1)) 
              #f -1)
            (trie #\e 
              (list
                (trie #\d empty #t -1)
                (trie #\l (list (trie #\l empty #t -1)) #f -1)
                (trie #\t empty #t -1)) 
          #t -1)) 
      #f -1)) 
#f -1))


;;; (pre-order-traverse testtrie)


(define inserted-words (list "bad" "bat" "bam" "bet" "bed" "bell"))
(define not-inserted-words (list "apple" "tomato" "cucumber" "b" "a" "m" "c" "l" "d" "t" ""))


(define lookup-tests
  (test-suite
    "Tests for lookup"
    (test-case
      "All the words inserted can be found"
      (for/list ([word inserted-words])
        (check-true (lookup testtrie word))))

    (test-case
      "Words not in the trie are not found"
      (for/list ([word not-inserted-words])
        (check-false (lookup testtrie word))))

    (test-case
      "Looking up 'be' in the tree"
      (check-true (lookup testtrie_after_insert_be "be")))
))


;;; debugging prints
;;;  (pre-order-traverse testtrie_after_insert_be)
;;;   (pre-order-traverse (insert testtrie "be" -1))

(pre-order-traverse (build-trie-from-list-of-words empty-trie inserted-words 0))

(define insert-tests
  (test-suite
    "Tests for insert"
      (test-case
        "Insert 'app' into trie"
          (check-true (equal? (insert testtrie "app" -1) testtrie_after_insert))
          (check-true (equal? (insert testtrie "be" -1) testtrie_after_insert_be))
          (check-true (equal? (build-trie-from-list-of-words empty-trie inserted-words 0)
                              better-testtrie)))))

(run-tests lookup-tests)
(run-tests insert-tests)

