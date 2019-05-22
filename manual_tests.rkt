#lang racket

(require "triev2.rkt")
(require rackunit)
(require rackunit/text-ui)

;;;;;;;;;;;;;;;;;;;;;;;;; TESTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; words in this test trie
;; bad, bat, bam, bet, bed, bell
(define testtrie
  (trie 
    void 
      (list
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t (string->list "bad"))
                (trie #\m empty #t (string->list "bam"))
                (trie #\t empty #t (string->list "bat"))) 
              #f (string->list "ba"))
            (trie #\e 
              (list
                (trie #\d empty #t (string->list "bed"))
                (trie #\l (list (trie #\l empty #t (string->list "bell"))) #f (string->list "bel"))
                (trie #\t empty #t (string->list "bet"))) 
          #f (string->list "be"))) 
      #f (string->list "b"))) 
#f empty))

;; trie after inserting the word "app"
(define testtrie_after_insert
  (trie 
    void 
      (list
        (trie #\a
          (list 
            (trie #\p 
              (list 
                (trie #\p empty #t (string->list "app"))) #f (string->list "ap")))
            #f (string->list "a"))
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t (string->list "bad"))
                (trie #\m empty #t (string->list "bam"))
                (trie #\t empty #t (string->list "bat")))
              #f (string->list "ba"))
            (trie #\e 
              (list
                (trie #\d empty #t (string->list "bed"))
                (trie #\l (list (trie #\l empty #t (string->list "bell"))) #f (string->list "bel"))
                (trie #\t empty #t (string->list "bet"))) 
          #f (string->list "be"))) 
      #f (string->list "b"))) 
#f empty))

;;; words in this test trie
;; bad, bat, bam, bet, bed, bell
(define testtrie_after_insert_be
  (trie 
    void 
      (list
        (trie #\b 
          (list
            (trie #\a 
              (list
                (trie #\d empty #t (string->list "bad"))
                (trie #\m empty #t (string->list "bam"))
                (trie #\t empty #t (string->list "bat")))
              #f (string->list "ba"))
            (trie #\e 
              (list
                (trie #\d empty #t (string->list "bed"))
                (trie #\l (list (trie #\l empty #t (string->list "bell"))) #f (string->list "bel"))
                (trie #\t empty #t (string->list "bet")))
          #t (string->list "be")))
      #f (string->list "b"))) 
#f empty))

;;; (pre-order-traverse testtrie)

(define inserted-words (list "bad" "bat" "bam" "bet" "bed" "bell"))
(define sorted-list (list "bad" "bam" "bat" "bed" "bell" "bet"))
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
;;(pre-order-traverse testtrie_after_insert_be)
;;(pre-order-traverse (insert testtrie "be"))

(define insert-tests
  (test-suite
    "Tests for insert"
      (test-case
        "Insert 'app' into trie"
          (check-true (equal? (insert testtrie "app") testtrie_after_insert))
          (check-true (equal? (insert testtrie "be") testtrie_after_insert_be))
          (check-true (equal? (build-trie-from-list-of-words empty-trie inserted-words)
                              testtrie)))))
                              
(define sort-tests 
  (test-suite
    "Tests for sort"
      (test-case  
        "Sort from a basic trie"
          (check-true (equal? (trie-sort inserted-words)
                            sorted-list)))))
                          
(run-tests lookup-tests)
(run-tests insert-tests)
(run-tests sort-tests)

