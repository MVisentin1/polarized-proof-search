From Stdlib Require Import List RelationClasses SetoidList.
From LJF Require Import SharedLogic Decidability 
    Pndctx Sequents Sets.

Fixpoint get_all_pairs_1 (a : list o) (LB : list o) : list ((list o) * o) :=
    match LB with
    | nil       => nil
    | b :: Lb   => (a, b) :: (get_all_pairs_1 a Lb)
    end
.

Lemma get_all_pairs_1_complete (a : list o) (LB : list o) :
    forall {b : o}, In b LB -> In (a, b) (get_all_pairs_1 a LB).
Proof.
    induction LB.
    - intros. inversion H.
    - intros. simpl. destruct (o_eq_dec a0 b).
        + subst. left. reflexivity.
        + right. apply IHLB. inversion H. contradiction. apply H0.
Qed.

Lemma get_all_pairs_1_inv (a : list o) {LB : list o} :
    forall {e : (list o) * o}, In e (get_all_pairs_1 a LB) -> a = fst e /\ In (snd e) LB.
Proof.
    induction LB.
    - intros. simpl in H. exfalso. apply H.
    - simpl. intros. destruct H.
        + destruct e. inversion H. subst. split.
            simpl. reflexivity.
            left. simpl. reflexivity.
        + split. apply IHLB. apply H. right. apply IHLB. apply H.
Qed.
    

Lemma get_all_pairs_1_sound (a : list o) {LB : list o} : 
    forall {b : o}, In (a, b) (get_all_pairs_1 a LB) ->  In b LB.
Proof.
    induction LB.
    - intros. simpl in*. apply H.
    - intros. simpl in*. destruct H. 
        + inversion H. subst. left. reflexivity.
        + right. apply IHLB. apply H.
Qed.

Fixpoint get_all_pairs (LA : list (list o)) (LB : list o) : list ((list o) * o) :=
    match LA with
    | nil       => nil
    | a :: La   => (get_all_pairs_1 a LB) ++ get_all_pairs La LB
    end
.

Definition visited_eq (C1 C2 : (list o) * o) : Prop :=
    set_eq (fst C1) (fst C2) /\ (snd C1) = (snd C2).

#[export] Instance visited_eq_Equivalence : Equivalence visited_eq.
Proof.
  split ; intros.
  - split. reflexivity. reflexivity.
  - split. symmetry. apply H. symmetry. inversion H. apply H1.
  - split. transitivity (fst y). apply H. apply H0. transitivity (snd y). apply H. apply H0.
Qed.

Lemma visited_eq_dec : forall {C1 C2 : (list o) * o}, {visited_eq C1 C2} + {~ visited_eq C1 C2}.
Proof.
    intros. unfold visited_eq.
    destruct (set_eq_dec o_eq_dec (fst C1) (fst C2)) ;
    destruct (o_eq_dec (snd C1) (snd C2)).
    - left. split. apply s. apply e.
    - right. intro. destruct H. contradiction.  
    - right. intro. destruct H. contradiction.  
    - right. intro. destruct H. contradiction.  
Qed. 

Lemma get_all_pairs_complete (LA : list (list o)) (LB : list o) :
    forall {a : list o} {b : o}, In a LA -> In b LB -> Exists (fun e => visited_eq e (a, b)) (get_all_pairs LA LB).
Proof.
    induction LA.
    - intros. inversion H.
    - intros. simpl. apply Exists_app. destruct H.
        + subst. left. apply Exists_exists. eexists. split.
            apply get_all_pairs_1_complete. apply H0. reflexivity.
        + right. apply IHLA. apply H. apply H0.
Qed.  

Lemma get_all_pairs_sound {LA : list (list o)} {LB : list o} :
    forall {e : (list o) * o}, (In e (get_all_pairs LA LB) -> In (fst e) LA /\ In (snd e) LB).
Proof.
    induction LA.
    - intros. simpl in*. exfalso. apply H.
    - intros. simpl in*. apply in_app_or in H. destruct H.
        ++ split. left. 
            eapply get_all_pairs_1_inv. apply H.
            eapply get_all_pairs_1_inv. apply H.
        ++ split. right.
            apply IHLA. apply H.
            apply IHLA. apply H.
Qed.

Definition get_all_visited (S: sequent) : list ((list o) * o) :=
    let per := sequent_subformulas_permeable S in
    let bra := sequent_subformulas_bracketable S in
    get_all_pairs (get_all_subsets per) bra.

Lemma get_all_visited_iff_subsequent :
    forall {C: pndctx} {K: o} {S : sequent},
        subsequent (Sept C nil K) S <-> Exists (fun e => visited_eq e (pndctx_list C, K)) (get_all_visited S).
Proof.
    intros. unfold get_all_visited. split.
    - intro. destruct H.
        assert (incl (pndctx_list C) (sequent_subformulas_permeable S)).
        + unfold incl. apply Forall_forall. apply H.
        + destruct (@get_all_subsets_complete _ o_eq_dec (sequent_subformulas_permeable S) (pndctx_list C)).
            clear H3. specialize (H2 H1).
            apply Exists_exists in H2. destruct H2. destruct H2.
            eapply Exists_impl.
            -- intros. transitivity (x, K).
                ++ apply H4.
                ++ unfold visited_eq. split. simpl. symmetry. apply H3.
                    simpl. reflexivity.
            -- destruct H0. apply (get_all_pairs_complete _ _ H2 H4).
    - intros. apply Exists_exists in H. destruct H. destruct H.
        apply get_all_pairs_sound in H. destruct H.
        inversion H0. simpl in H2. simpl in H3. subst.
        unfold subsequent. split.
        + apply Forall_forall.
            assert (incl (fst x) (sequent_subformulas_permeable S)).
            -- apply (proj2 (@get_all_subsets_complete _ o_eq_dec
                            (sequent_subformulas_permeable S) (fst x))).
                apply Exists_exists. exists (fst x). split.
                ++ exact H.
                ++ reflexivity.
            -- intros. apply H3. unfold set_eq in H2. destruct H2. apply H5. apply H4.
        + split.
            -- apply Forall_nil.
            -- apply H1.
Qed.


        

            
         
        

        

           
            



        
        




    