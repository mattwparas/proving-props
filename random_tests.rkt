#lang racket

(require "triev2.rkt")
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
          (make-random-list-of-unique-strings alphabet))))))

(define random-sort-tests
  (test-suite
    "Tests for randomly sorting lists of strings"
    (test-case "First random test"
      (for ([i 5000])
        (define strings (make-random-list-of-unique-strings alphabet)) 
        (trie-sort strings)))))

;; these require some refinement
(define random-lookup-tests
  (test-suite
   "Tests for correctly looking up words in the trie and words not in the trie"
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
                                    list1))
                (check-true (for/and ([word list1])
                              (lookup built-trie word)))
                (check-false (for/and ([word list2])
                               (lookup built-trie word)))))))

(define tree-is-deterministic
  (test-suite
    "Test to see if insert produces the same sorted list with a different insertion order"
    (test-case "Deterministic test"
              (for ([i 100])
                (define list-of-strings (make-random-list-of-unique-strings alphabet))
                (define shuffled-list-of-strings (shuffle list-of-strings))
                ; (define trie1 (build-trie-from-list-of-words 
                ;     empty-trie
                ;     list-of-strings))
                ; (define trie2 (build-trie-from-list-of-words
                ;     empty-trie
                ;     shuffled-list-of-strings))
                (define sorted-list-1 
                  (trie-sort list-of-strings))
                (define sorted-list-2 
                  (trie-sort shuffled-list-of-strings))
                (check-true (equal? sorted-list-1 sorted-list-2))))))

(define trie-construction-returns-the-same-tree
  (test-suite
    "Test to see if inserting the same words in the same order produces the samea tree"
      (test-case "Same tree test"
        (for ([i 100])
          (define list-of-strings (make-random-list-of-unique-strings alphabet))
          (define trie1 (build-trie-from-list-of-words
            empty-trie
            list-of-strings))
          (define trie2 (build-trie-from-list-of-words
            empty-trie
            list-of-strings))
          (check-true (equal? trie1 trie2))))))

;; test suite
(run-tests random-trie-tests)
(run-tests random-sort-tests)
(run-tests random-lookup-tests)
(run-tests tree-is-deterministic)
(run-tests trie-construction-returns-the-same-tree)
