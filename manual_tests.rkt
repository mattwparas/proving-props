#lang racket

(require "trie.rkt")
(require rackunit)
(require rackunit/text-ui)

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
;;;  (pre-order-traverse testtrie_after_insert_be)
;;;   (pre-order-traverse (insert testtrie "be" -1))

(define insert-tests
  (test-suite
    "Tests for insert"
      (test-case
        "Insert 'app' into trie"
          (check-true (equal? (insert testtrie "app" -1) testtrie_after_insert))
          (check-true (equal? (insert testtrie "be" -1) testtrie_after_insert_be))
          (check-true (equal? (build-trie-from-list-of-words empty-trie inserted-words 0)
                              better-testtrie)))))
                              
(define sort-tests 
  (test-suite
    "Tests for sort"
      (test-case  
        "Sort from a basic trie"
          (check-true (equal? (trie-sort
                                    (build-trie-from-list-of-words empty-trie inserted-words 0) 
                                    inserted-words)
                            sorted-list)))))
                          
(run-tests lookup-tests)
(run-tests insert-tests)
(run-tests sort-tests)

