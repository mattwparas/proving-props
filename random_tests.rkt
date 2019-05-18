#lang racket

(require "trie.rkt")
(require rackunit)
(require rackunit/text-ui)


;;;;;;;;;;;;;;;;; Random tests baby ;;;;;;;;;;;;;;;;;;


;; This next section, courtesy of Robby Findler
;; https://groups.google.com/forum/#!topic/racket-users/FKmJzL1zIZw
(provide 
 (contract-out 
  [make-a-string (-> non-empty-string? string?)]
  [make-random-list-of-strings (-> non-empty-string? (listof string?))]
  [make-random-list-of-unique-strings (-> (listof string?) (listof string?))])) 

(define alphabet "abcdefghijklmnopqrstuvwxyz")

(define (make-a-string candidates) 
  (apply 
   string 
   (for/list ([i (in-range (random 1 100))]) 
     (string-ref candidates (random (string-length candidates)))))) 

(define (make-random-list-of-strings candidates)
  (for/list ([i (in-range (random 1 100))])
    (make-a-string candidates)))

(define (make-random-list-of-unique-strings candidates)
  (remove-duplicates (make-random-list-of-strings candidates)))


(define (generate-list-of-length>2 input-list)
  (if (<= (length input-list) 2)
      (generate-list-of-length>2 (make-random-list-of-unique-strings alphabet))
      input-list))

(module+ test
  (require rackunit)
  (check-true (string? (make-a-string alphabet)))
  (check-true 
    ((listof string?)
    (make-random-list-of-strings alphabet)))
  (check-true 
    ((listof string?)
    (make-random-list-of-unique-strings alphabet))))


(define random-trie-tests
  (test-suite
    "Tests for randomly building tries"
    (test-case "First random test"
      (for ([i 5000])
        (build-trie-from-list-of-words 
          empty-trie
          (make-random-list-of-unique-strings alphabet)
          0)))))

(define random-sort-tests
  (test-suite
    "Tests for randomly sorting lists of strings"
    (test-case "First random test"
      (for ([i 5000])
        (define strings (make-random-list-of-unique-strings alphabet)) 
        (trie-sort (build-trie-from-list-of-words 
          empty-trie
          strings
          0) strings)))))


;; these require some refinement
(define random-lookup-tests
  (test-suite
   "Tests for looking up words inserted into trie when "
   (test-case "First random test"
              (for ([i 100])
                (define start-list (make-random-list-of-unique-strings alphabet))
                (define list-of-strings (generate-list-of-length>2 start-list))
                (define split-index (random 1 (- (length list-of-strings) 1)))
                (define list1 (map (lambda (index) (list-ref list-of-strings index))
                                   (range split-index)))
                (define list2 (map (lambda (index) (list-ref list-of-strings index))
                                   (range split-index (length list-of-strings))))
                (define built-trie (build-trie-from-list-of-words
                                    empty-trie
                                    list1
                                    0))
                (check-true (for/and ([word list1])
                              (lookup built-trie word)))
                (check-false (for/and ([word list2])
                               (lookup built-trie word)))))))


;(run-tests random-trie-tests)
;(run-tests random-sort-tests)

(run-tests random-lookup-tests)

;;; (require test)

;;; (make-a-string "abcdefghijklmnopqrstuvwxyz")

;;; (make-random-list-of-strings "abcdefghijklmnopqrstuvwxyz")