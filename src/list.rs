use vstd::prelude::*;
verus! {


    // List<T> is a singly linked list
    struct LList<T>{
        head: Option<Box<Node<T>>>,
        len: usize,
    }

    struct Node<T>{
        data: T,
        next: Option<Box<Node<T>>>,
    }


    impl<T> Node<T> {

        // this terminates on a null-terminated node
        spec fn optional_as_seq(node_opt: Option<Box<Node<T>>>) -> Seq<Node<T>>
            decreases node_opt, // demonstrate that recursion will terminate
        {
            match node_opt {
                None       => Seq::empty(),
                Some(node) => node.as_seq(),
            }
        }

        // **Taken from Verus Tutorial on Treemap. Unsure how this works to interpret the linked list as a Seq**
        spec fn as_seq(self) -> Seq<Node<T>>
            decreases self,
        {
            // Node<T>::optional_as_seq(self.next).insert(self.data)
            seq![self] + Node::<T>::optional_as_seq(self.next)
        }
        /*
         * This proof is similar to the converse of lemma_next_index.
         * It lets us prove whether or not a given node's has a next
         * pointer based on knowledge the length of its .as_seq() view.
         *
         * The main place where this is tricky is proving that if
         * self.as_seq().len() == 1, then the next pointer must be None.
         * We do this via proof by contradiction.
         */
        proof fn lemma_len_match(self)
            ensures
                self.as_seq().len() == 1 ==> self.next is None,
                self.as_seq().len() > 1 ==> self.next is Some
        {
            let s = self.as_seq();
            if s.len() == 1 {
                if let Some(node) = self.next {
                    // proof by contradiction. We know that since s.len() == 1, the following
                    // assertion must hold.
                    assert(Node::<T>::optional_as_seq(self.next).len() == 0);
                    // however, according to the current match branch, self.next is Some, which means
                    // node.as_seq() is valid and non-empty.
                    assert(node.as_seq() == seq![*node] + Node::<T>::optional_as_seq(node.next));
                    // but these can't both be true, so we have a contradiction
                    assert(false);
                }
            }
            // the proof is trivial when self.as_seq().len() > 1.
        }


        /* This proof establishes that if the current node has a next pointer,
         * then the second element of its view from .as_seq() is the next node.
         * If the current node does not have a next pointer, then its .as_seq()
         * view only has one element.
         * Verus also needs a little push to prove that the first element of
         * self.as_seq() is self, so we do that here too.
         */
        proof fn lemma_as_seq_contents(self)
            ensures
                self.as_seq()[0] == self,
                self.next is Some ==> self.as_seq()[1] == self.next.unwrap(),
                self.next is None ==> self.as_seq().len() == 1,
        {
            assert(self.as_seq() == seq![self] + Node::<T>::optional_as_seq(self.next));
            if self.next is Some {
                assert(self.as_seq()[0] == self);
                assert(Node::<T>::optional_as_seq(self.next) ==
                    seq![*self.next.unwrap()] + Node::<T>::optional_as_seq(self.next.unwrap().next));
            }
        }
    }

    impl<T> LList<T> {

        // do not show body outside module. This means that calls to this outside module
        // will not know as)seq calls optional_as_seq, which returns Seq<T>
        pub closed spec fn as_seq(self) -> Seq<Node<T>> {
            Node::<T>::optional_as_seq(self.head)
        }

        /* This proof helps establish that traversing our linked list will obtain
         * the same values as iterating over its view.
         * We do this by reasoning about how calls to .as_seq() form subranges of
         * the view of the linked list.
         *
         * This lemma does NOT actually have to be inductive! It's useful to think
         * of it as having a structure similar to an inductive proof, but it doesn't
         * need to make a recursive call, because we're going to use it inside a loop.
         */
        proof fn lemma_view_values_equals_subrange(self, i: int, current_node: Node<T>, s: Seq<Node<T>>)
            requires
                0 <= i < self.len,
                self@.len() == self.len,
                current_node == self@[i],
                // The sequence s is both the subrange of self@ from i to the end of self@,
                // and current_node.as_seq(). This is true at the call site because i == 0
                // and current_node is self.head, so s is just self@.s
                s == self@.subrange(i, self@.len() as int),
                s == current_node.as_seq(),
            ensures
                current_node.next is Some ==>
                    current_node.next.unwrap().as_seq() == self@.subrange(i + 1, self@.len() as int)
        {
            if self.len - 1 - i == 0 {
                // In this case, current_node is the last node in the list, so
                // current_node.next is None. Proving this will satisfy the postcondition,
                // but Verus needs a little help getting there.

                // These assertions are not required but are here for documentation.
                assert(self@.subrange(i, self@.len() as int).len() == 1); // Via arithmetic, we know the length of this subrange is 1
                assert(current_node.as_seq().len() == 1);                 // so current_node.as_seq() must also contain 1 element

                // Now, we can use lemma_len_match to prove that current_node.next is None when current_node.as_seq.len() == 1.
                // We just showed that, so we can now conclude that current_node.next is None.
                current_node.lemma_len_match();
                assert(current_node.next is None); // not required, just for documentation
            } else {
                // Here, we know that current_node.next is Some.
                // To prove the postcondition, we need to establish that current_node.next.as_seq()
                // is equivalent to self@.subrange(i + 1, self@.len() as int).

                // This simply requires a couple of assertions that force Verus to do some
                // extensional equality checks.
                // We know from the precondition that `s == self@.subrange(i, self@.len())`,
                // so this assertion follows via extensional equality.
                assert(s.subrange(1, s.len() as int) == self@.subrange(i + 1, self@.len() as int));
                // We also know that `s == current_node.as_seq()` from the precondition.
                // By definition, current_node.next.unwrap().as_seq() is current_node.as_seq()
                // minus the first element, which is obviously equivalent to s.subrange(1, s.len() as int)
                // via extensional equality.
                assert(s.subrange(1, s.len() as int) == current_node.next.unwrap().as_seq());
            }
        }
    }

    impl<T> View for LList<T> {
        type V = Seq<Node<T>>;

        // the view of the LList should be a sequence. This needs to be open so it is usable by
        // outside module
        open spec fn view(&self) -> Self::V {
            self.as_seq() // IS THIS TREATED LIKE "closed" HERE?
        }
    }

    // executable functionality
    impl<T> LList<T> {
        fn new() -> (out: Self)
            ensures out@.len() == 0, // empty
        {
            Self {
                head: None,
                len: 0
            } // return empty list
        }

        // This lemma proves that seq@[0] is the head node if the list
        // is not empty. This seems obvious, but proving it requires extensional
        // equality and appealing to the definition of as_seq(), so the proof
        // is not trivial.
        proof fn lemma_head_first_in_view_seq(self)
            requires
                self.len == self@.len(),
                self.len > 0,
            ensures
                self@[0] == self.head.unwrap()
        {
            assert(self.head is Some);
            assert(self@ == seq![*self.head.unwrap()] + Node::<T>::optional_as_seq(self.head.unwrap().next));
        }

        //TODO: Add proof function to show sequence is equivalent to linked list
        fn get(&self, index: usize) -> (out: &T)
            requires
                self.len == self@.len(),
                index < self@.len()
            ensures
                self@[index as int].data == out
        {

            let mut temp = self.head.as_ref().unwrap();
            let mut curr_index = 0;

            // First, we prove that the loop invariant holds before the beginning of
            // the loop. To do so, we need to prove that `temp == self@[0]`,
            // which we have a lemma for. We also need to use extensional equality
            // to prove that self@.subrange(curr_index as int, self@.len() as int)
            // is initially equal to self@; this is true because curr_index == 0,
            // so the subrange includes the entire sequence.
            proof {
                self.lemma_head_first_in_view_seq(); // proves that temp == self@[0]
                assert(self@ == self@.subrange(curr_index as int, self@.len() as int));
            }

            while (curr_index < index)
                invariant
                    // curr_index may be equal to index after the last iteration, but both
                    // curr_index and index are always less than self.len.
                    curr_index <= index < self.len,
                    self.len == self@.len(),
                    // The two remaining invariants satisfy the precondition of
                    // `lemma_view_values_equals_subrange`.
                    temp.as_seq() == self@.subrange(curr_index as int, self@.len() as int),
                    self@[curr_index as int] == temp
            {
                // First, we'll invoke `lemma_view_values_equals_subrange` to prove that
                // the subrange-based loop invariant is maintained after incrementing curr_index
                // and moving temp to temp.next.
                proof {
                    self.lemma_view_values_equals_subrange(
                        curr_index as int,
                        **temp,
                        self@.subrange(curr_index as int, self@.len() as int)
                    );
                }
                temp = temp.next.as_ref().unwrap();
                curr_index += 1;

                proof {
                    // We have not yet established that `self@[curr_index as int] == temp` for the new curr_index
                    // and temp. From `lemma_view_values_equals_subrange`, we know that the following assertion holds.
                    assert(temp.as_seq() == self@.subrange(curr_index as int, self@.len() as int)); // documentation assertion, not required.
                    // Which then implies the following assertion:
                    assert(temp.as_seq()[0] == self@.subrange(curr_index as int, self@.len() as int)[0]); // documentation assertion, not required.
                    // Clearly `self@[curr_index] == self@.subrange(curr_index as int, self@.len() as int)[0]`, so
                    // we can finish up by proving that `temp.as_seq()[0] == temp`, which lemma_as_seq_contents will do.
                    temp.lemma_as_seq_contents();
                }
            }
            return &temp.data;
        }
    }

} // verus!
