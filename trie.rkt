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

;; is the trie composed of values on the edges
;;; (struct root-trie (children))

;; contract: trie list-of-characters -> bool
(define (lookup-helper trie-node char-list)
  (cond
  [(empty? char-list) #f] ; hit the case where its empty
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
  


;;; ;; contract: list-of-characters character -> list-of-characters
;;; (define (create-chars lst value) 
;;;   (cond [(empty? lst)          ; if the list is empty
;;;          (list value)]        ; then return a single-element list
;;;         [(char<=? value (first lst)) ; if current element >= value
;;;          (cons value lst)]   ; insert value in current position
;;;         [else                 ; otherwise keep building the list
;;;          (cons (first lst)      ; by adding current element
;;;                (create-chars value (rest lst)))])) ; and advancing recursion)

;;(struct trie (char children end-word? index))
;; contract: list-of-chars list-of-tries inte-> list-of-tries
(define (create-children char-list lst index)
  (cond [(= (length char-list) 1)
              (cond [(empty? lst) 
              ;;; (displayln "empty lst, char 1")
                        (list (trie (first char-list) empty #t index))]
                    [(char<? (first char-list) (trie-char (first lst)))
                    ;;; (displayln "char<, char 1") 
                        (cons (trie (first char-list) empty #t index) lst)]
                    [(char=? (first char-list) (trie-char (first lst)))
                    ;;; (displayln "char=, char 1") 
                        (cons (trie (first char-list) (trie-children (first lst)) #t index) (rest lst))]
                    [else
                    ;;; (displayln "move to next child, char 1") 
                        (cons (first lst)
                              (create-children char-list (rest lst) index))])]
        [else ;; you are in the middle of the word
              (cond [(empty? lst) 
                        (list (trie (first char-list) (create-children 
                                                          (rest char-list) empty index) #f -1))]
                    [(char<? (first char-list) (trie-char (first lst)))
                    ;;; (println "bopppppppp")
                        (cons (trie (first char-list) (create-children 
                                                          (rest char-list) empty index) #f -1) lst)]
                    [(char=? (first char-list) (trie-char (first lst)))
                        (cons (trie (first char-list) (trie-children (first lst)) #f -1) (rest lst))]
                    [else
                        (cons (first lst)
                              (create-children char-list (rest lst) index))])]))

;; contract: trie string integer -> trie
(define (insert root-trie word index)
  (define char-list (string->list word))
  (displayln "Inserting word into trie")
  (trie 
    (trie-char root-trie)
      (create-children char-list (trie-children root-trie) index)
      (trie-end-word? root-trie)
      (trie-index root-trie)))


;; contract: trie char -> bool
(define (trie<=? trie1 char)
  (char<=? char (trie-char trie1)))


;;; (define test-list (list #\a #\b #\d #\e))

;;; (insert #\c test-list)

(define (pre-order-traverse trie-node)
  (displayln (trie-char trie-node))
  (map pre-order-traverse (trie-children trie-node))
  "finished"
)

;; copies the remainder of the trie from the given node
;; contract: trie -> trie
(define (copy trie-node)
  (trie
    (trie-char trie-node)
    (map copy (trie-children trie-node))
    (trie-end-word? trie-node)
    (trie-index trie-node)))



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
#t -1))

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
#t -1))

;;; (pre-order-traverse testtrie)


(define inserted-words (list "bed" "bat" "bam" "bet" "bed" "bell"))
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
))


(define copy-test-trie (copy testtrie))
(define copy-lookup-tests
  (test-suite
    "Tests for lookup"
    (test-case
      "All the words inserted can be found"
      (for/list ([word inserted-words])
        (check-true (lookup copy-test-trie word))))

    (test-case
      "Words not in the trie are not found"
      (for/list ([word not-inserted-words])
        (check-false (lookup copy-test-trie word))))

    (test-case
      "Check equality of copy"
      (check-true (equal? copy-test-trie testtrie)))
))

 (pre-order-traverse testtrie_after_insert)
  (pre-order-traverse (insert testtrie "app" -1))

(define insert-tests
  (test-suite
    "Tests for insert"
      (test-case
        "Insert 'app' into trie"
          (check-true (equal? (insert testtrie "app" -1) testtrie_after_insert)))))

(run-tests lookup-tests)
(run-tests copy-lookup-tests)
(run-tests insert-tests)

;; ----------------------------------------- garbage?

;;; (define file-tests
;;;   (test-suite
;;;    "Tests for file.rkt"
 
;;;    (check-equal? (+ 1 1) 2 "Simple addition")
 
;;;    (check-equal? (* 1 2) 2 "Simple multiplication")
 
;;;    (test-case
;;;     "List has length 4 and all elements even"
;;;     (let ([lst (list 2 4 6 8)])
;;;       (check = (length lst) 4)
;;;       (for-each
;;;         (lambda (elt)
;;;           (check-pred even? elt))
;;;       lst)))))



;; stub
;;; (define (insert-helper trie char-list index)
;;;   (cond
;;;   [(not (char=? (first char-list) (trie-char trie-node))) 
;;;     (copy trie-node)]
;;;   []
;;;   )
;;;   #t)

;;; ;; main function for insert
;;; ;; takes the rooted trie and sets it on its path
;;; (define (insert root-trie word index)
;;;   (define char-list (string->list word))
;;;   (trie
;;;     (trie-char root-trie) ; should always be void
;;;     (map (lambda (trie-node)
;;;           (if (char=? (trie-char trie-node) (first char-list)
;;;             (insert-helper trie-node char-list index) ; if the characters match, call helper
;;;             (copy char-start)))) ; if the characters dont match, just copy the rest of that
;;;           (trie-children root-trie)) ;; set up the children
;;;     (trie-end-word? root-trie) ; should always be false
;;;     (trie-index root-trie) ; should always be -1
;;;   )
;;; )

















