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
   (for/list ([i (in-range (random 1 11))]) 
     (string-ref candidates (random (string-length candidates)))))) 

(define (make-random-list-of-strings candidates)
  (for/list ([i (in-range (random 1 11))])
    (make-a-string candidates)))

(define (make-random-list-of-unique-strings candidates)
  (remove-duplicates (make-random-list-of-strings candidates)))

(module+ test
  (require rackunit)
  (check-true (string? (make-a-string alphabet)))
  (check-true 
    ((listof string?)
    (make-random-list-of-strings alphabet)))
  (check-true 
    ((listof string?)
    (make-random-list-of-unique-strings alphabet))))


(define test-strings (make-random-list-of-unique-strings alphabet))

;;; (displayln test-strings)

(for ([str test-strings])
  (displayln (list str (string-length str))))
(displayln "done")

(define random-trie-tests
  (test-suite
    "Tests for randomly building tries"
    (test-case "First random test"
      (for ([i 10])
        (build-trie-from-list-of-words 
          empty-trie
          test-strings
          0)))))


(run-tests random-trie-tests)

;;; (require test)

;;; (make-a-string "abcdefghijklmnopqrstuvwxyz")

;;; (make-random-list-of-strings "abcdefghijklmnopqrstuvwxyz")