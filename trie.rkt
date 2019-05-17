#lang racket

(require rackunit)
(require rackunit/text-ui)


;; char -> character
;; children -> list of tries
;; assume the list of children is ordered?
;; end-word? -> bool
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

(run-tests lookup-tests)

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



















