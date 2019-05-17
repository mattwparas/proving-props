#lang racket

(require rackunit)

;; node -> root
;;; (struct Trie (root))

;; char -> character
;; children -> list of tries
;; assume the list of children is ordered?
;; end-word? -> bool
(struct trie (char children end-word?))

;; is the trie composed of values on the edges
(struct root-trie (children))



(define (lookup-helper trie-node char-list)
  ;;; (displayln char-list)
  (cond
  [(empty? char-list) #f] ; hit the case where its empty
  [(not (char=? (first char-list) (trie-char trie-node))) #f]
  [(= (length char-list) 1) ; return if its an end word
    ;;; (displayln char-list)
    (trie-end-word? trie-node)]
  [else
    (for/first ([i (trie-children trie-node)]
    #:when (char=? (first (rest char-list)) (trie-char i)))
    (lookup-helper i (rest char-list)))]))

(define (lookup root-trie word)
  (for/first ([i (root-trie-children root-trie)]
  #:when (char=? (first (string->list word)) (trie-char i)))
  (lookup-helper i (string->list word))))


;;; words in this test trie
;; bad, bat, bam, bet, bed, bell
(define testtrie
  (root-trie 
    (list
      (trie #\b 
        (list
          (trie #\a 
            (list
              (trie #\d empty #t)
              (trie #\t empty #t)
              (trie #\m empty #t)) 
          #f)
          (trie #\e 
            (list
              (trie #\t empty #t)
              (trie #\d empty #t)
              (trie #\l 
                (list
                  (trie #\l empty #t))
              #f)) 
          #t))
      #f))
  ))

;;; (trie-char testtrie)

(define inserted-words (list "bed" "bat" "bam" "bet" "bed" "bell"))
(define not-inserted-words (list "apple" "tomato" "cucumber" "b" "a" "m" "c" "l" "d" "t"))
(for/list ([word inserted-words])
  (check-true (lookup testtrie word)))
(for/list ([word not-inserted-words])
  (check-false (lookup testtrie word)))

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


;;; (require rackunit/text-ui)

;;; (run-tests file-tests)




















