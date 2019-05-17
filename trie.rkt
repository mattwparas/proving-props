#lang racket

(require rackunit)
(require rackunit/text-ui)


;; char -> character
;; children -> list of tries
;; assume the list of children is ordered? maybe?
;; end-word? -> bool
;; index -> index of word in the original list
(struct trie (char children end-word? index))

;; is the trie composed of values on the edges
;;; (struct root-trie (children))


(define (lookup-helper trie-node char-list)
  (cond
  [(empty? char-list) #f] ; hit the case where its empty
  [(not (char=? (first char-list) (trie-char trie-node))) #f]
  [(= (length char-list) 1) ; return if its an end word
    (trie-end-word? trie-node)] ; #t or #f here
  [else
    (for/first ([i (trie-children trie-node)]
      #:when (char=? (first (rest char-list)) (trie-char i)))
      (lookup-helper i (rest char-list)))])) ; recur on the child which matches character

(define (lookup root-trie word)
  (for/first ([i (trie-children root-trie)]
    #:when (char=? (first (string->list word)) (trie-char i)))
    (lookup-helper i (string->list word))))
  
;; copies the remainder of the trie from the given node
(define (copy trie-node)
  (trie
    (trie-char trie-node)
    (map copy (trie-children trie-node))
    (trie-end-word? trie-node)
    (trie-index trie-node)
  )
)

;; stub
(define (insert-helper trie char-list index)
  #t)

;; main function for insert
;; takes the rooted trie and sets it on its path
(define (insert root-trie word index)
  (define char-list (string->list word))
  (trie
    (trie-char root-trie) ; should always be void
    (map (lambda (trie-node)
          (if (char=? (trie-char trie-node) (first char-list)
            (insert-helper trie-node char-list index) ; if the characters match, call helper
            (copy char-start)))) ; if the characters dont match, just copy the rest of that
          (trie-children root-trie)) ;; set up the children
    (trie-end-word? root-trie) ; should always be false
    (trie-index root-trie) ; should always be -1
  )
)



  (for/list ([char-start (trie-children root-trie)]
    (if (char=? char-start (first char-list))
      (insert-helper char-start char-list index) ; start using the helper on that branch
      (copy char-start) ; otherwise copy the branch all the way down
      )
  ))

(define (pre-order-traverse trie-node)
  (displayln (trie-char trie-node))
  (map pre-order-traverse (trie-children trie-node))
  "finished"
)



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
                (trie #\t empty #t -1)
                (trie #\m empty #t -1)) 
            #f -1)
            (trie #\e 
              (list
                (trie #\t empty #t -1)
                (trie #\d empty #t -1)
                (trie #\l 
                  (list
                    (trie #\l empty #t -1))
                #f -1)) 
            #t -1))
        #f -1))
    #f -1)
)

(pre-order-traverse testtrie)

(define inserted-words (list "bed" "bat" "bam" "bet" "bed" "bell"))
(define not-inserted-words (list "apple" "tomato" "cucumber" "b" "a" "m" "c" "l" "d" "t"))


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
))

(run-tests lookup-tests)
(run-tests copy-lookup-tests)

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



















