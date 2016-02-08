Inductive OP : Set := O | P.
Inductive QA : Set := Q | A.

Hint Constructors OP.
Hint Constructors QA.

Section Arena.

  Variable M : Type.

  Definition labelling := M -> (OP * QA).

  Definition l_OP (l : labelling) : M -> OP := fun m => fst (l m).
  Definition l_QA (l : labelling) : M -> QA := fun m => snd (l m).

  Definition inv (l : labelling) : labelling := 
    fun m => 
      let (op, qa) := l m in
      (match op with O => P | _ => O end, qa).

  Lemma inv_preserves_qa : 
    forall (l : labelling) (m : M) (qa : QA), snd (inv l m) = snd (l m).
  Proof. admit. Qed.

  Lemma inv_bijective_po : 
    forall (l : labelling) (m n : M), fst (inv l m) = fst (inv l n) -> fst (l m) = fst (l n).
  Proof. admit. Qed.

  Definition enabling := option M -> M -> Prop.
  
  Definition start_OQ (l : labelling) (e : enabling) :=
    forall (m : M), e None m -> l m = (O, Q) /\ forall (n : option M), e n m -> n = None.

  Definition A_to_Q (l : labelling) (e : enabling) :=
    forall (m n : M), e (Some m) n -> l_QA l n = A -> l_QA l m = Q.

  Definition P_to_O (l : labelling) (e : enabling) :=
    forall (m n : M), e (Some m) n -> l_OP l n <> l_OP l m.

  Definition unique_justifier (l : labelling) (e : enabling) :=
    forall (l m n : M), e (Some l) n -> e (Some m) n -> m = l. 

  Inductive arena : labelling -> enabling -> Prop := 
    mk_arena (l : labelling) (e : enabling) : 
      start_OQ l e /\ A_to_Q l e /\ P_to_O l e (*/\ unique_justifier l e*) -> arena l e.

  Ltac deconj :=    
    match goal with
      H : _ /\ _ |- _ => inversion_clear H; try deconj
    end.

  Definition arena_start (l : labelling) (e : enabling) : arena l e -> start_OQ l e.
  Proof. intro A. inversion A. deconj. assumption. Qed.

  Definition arena_AQ (l : labelling) (e : enabling) : arena l e -> A_to_Q l e.
  Proof. intro A. inversion A. deconj. assumption. Qed.

  Definition arena_PO (l : labelling) (e : enabling) : arena l e -> P_to_O l e.
  Proof. intro A. inversion A. deconj. assumption. Qed.
(*
  Definition arena_unique_justifier (l : labelling) (e : enabling) : arena l e -> unique_justifier l e.
  Proof. intro A. inversion A. deconj. assumption. Qed.
*)
End Arena.

Module Type ARENA.
  Parameter M     : Type.
  Parameter lab   : labelling M.
  Parameter enab  : enabling M.
  Parameter arena : arena M lab enab.
End ARENA.

Module Type TYPE.
  Parameter T : Type.
End TYPE.

Module ConstArena (T : TYPE) : ARENA.

  Inductive M_ := TQ | TT : T.T -> M_.

  Definition M := M_.

  Definition lab : labelling M := fun n =>
    match n with
    | TQ => (O, Q)
    | _  => (P, A)
    end. 

  Inductive enab_ : enabling M := 
  | StartNat  : enab_ None TQ
  | AnswerNat : forall (t : T.T), enab_ (Some TQ) (TT t).

  Definition enab := enab_.

  Lemma start_OQ_ok : start_OQ M lab enab.
  Proof.
    unfold start_OQ. intros M H. split. 
      inversion_clear H. reflexivity. 
      intros n H1. inversion H as [|H2]. rewrite <-H2 in H1. inversion H1. reflexivity. 
  Qed.

  Lemma A_to_Q_ok : A_to_Q M lab enab.
  Proof.
    unfold A_to_Q. intros m n H A. inversion H. reflexivity.
  Qed.

  Lemma P_to_O_ok : P_to_O M lab enab.
  Proof.
    unfold P_to_O. intros m n H. unfold not. intro E. inversion H as [H0|H1]. 
      rewrite <- H2 in E. rewrite <- H0 in E. inversion E.
  Qed.
(*
  Lemma unique_justifier_ok : unique_justifier M lab enab.
  Proof.
    unfold unique_justifier. intros l m n G H. inversion G. inversion H. reflexivity.
  Qed.
*)           
  Hint Resolve start_OQ_ok A_to_Q_ok P_to_O_ok (*unique_justifier_ok*).

  Definition arena : arena M lab enab.
  Proof.
    apply mk_arena; split; auto.
  Qed.

End ConstArena.

Module NAT.
  Definition T := nat.
End NAT.

Module NatArena := ConstArena NAT.

Module ProdArena (X Y : ARENA) : ARENA.

  Inductive M_ := Left : X.M -> M_ | Right : Y.M -> M_.

  Definition M := M_.

  Definition lab : labelling M := fun n =>
    match n with
    | Left  x => X.lab x
    | Right y => Y.lab y
    end. 

  Inductive enab_ : enabling M := 
  | StartX : forall (x : X.M), X.enab None x -> enab_ None (Left  x)
  | StartY : forall (y : Y.M), Y.enab None y -> enab_ None (Right y)
  | TransX : forall (x y : X.M), X.enab (Some x) y -> enab_ (Some (Left  x)) (Left  y)
  | TransY : forall (x y : Y.M), Y.enab (Some x) y -> enab_ (Some (Right x)) (Right y).

  Definition enab := enab_.

  Lemma start_OQ_ok : start_OQ M lab enab.
  Proof. 
    unfold start_OQ. intros m H. destruct m; (
      inversion H as [H0|H1|H2|H3];
        try apply (arena_start X.M X.lab X.enab X.arena) in H2;
        try apply (arena_start Y.M Y.lab Y.enab Y.arena) in H2;
        inversion_clear H2 as [H4];
        split; [ simpl; assumption |
                 intros n E; inversion E as [H5|H6|H7|H8]; [ reflexivity |
                                                             apply H3 in H6; inversion H6]
               ]
    ).
  Qed.

  Lemma A_to_Q_ok : A_to_Q M lab enab.
  Proof.
    unfold A_to_Q. intros m n E A. destruct n;
      (inversion_clear E; 
         try apply (arena_AQ X.M X.lab X.enab X.arena) in H; 
         try apply (arena_AQ Y.M Y.lab Y.enab Y.arena) in H;
         unfold l_QA in *; apply H in A; simpl; assumption
      ).
  Qed.

  Lemma P_to_O_ok : P_to_O M lab enab.
  Proof.
    unfold P_to_O. intros m n H. unfold not. intro Eq. destruct n; (
      inversion H; try apply (arena_PO X.M X.lab X.enab X.arena) in H2; 
                   try apply (arena_PO Y.M Y.lab Y.enab Y.arena) in H2; 
      unfold not in H2; apply H2; unfold l_OP in *; simpl in *; 
      rewrite <- H0 in Eq; simpl in Eq; assumption
    ).
  Qed.
(*
  Lemma unique_justifier_ok : unique_justifier M lab enab.
  Proof. 
    unfold unique_justifier. intros l m n EL EM. destruct n; (
      inversion EL; inversion EM; 
      try apply (arena_unique_justifier X.M X.lab X.enab X.arena x x0 m0) in H1; 
      try apply (arena_unique_justifier Y.M Y.lab Y.enab Y.arena x x0 m0) in H1; [ 
        rewrite H1; reflexivity 
      | assumption
      ]
    ).
  Qed.
*)
  Hint Resolve start_OQ_ok A_to_Q_ok P_to_O_ok (*unique_justifier_ok*).

  Definition arena : arena M lab enab.
  Proof.
    apply mk_arena; split; auto.
  Qed.
  
End ProdArena.

Module ExpArena (X Y : ARENA) : ARENA.

  Inductive M_ := Dom : X.M -> M_ | Cod : Y.M -> M_.

  Definition M := M_.

  Definition lab : labelling M := fun n =>
    match n with
    | Dom x => inv X.M X.lab x
    | Cod y => Y.lab y
    end.

  Inductive enab_ : enabling M :=
  | DomE  : forall (x y : X.M), X.enab (Some x) y -> enab_ (Some (Dom x)) (Dom y)
  | CodE  : forall (x y : Y.M), Y.enab (Some x) y -> enab_ (Some (Cod x)) (Cod y)
  | Codom : forall (x : X.M) (y : Y.M), X.enab None x -> Y.enab None y -> enab_ (Some (Cod y)) (Dom x)
  | Start : forall (y : Y.M), Y.enab None y -> enab_ None (Cod y).

  Definition enab := enab_.

  Lemma start_OQ_ok : start_OQ M lab enab.
  Proof. 
    unfold start_OQ. intros m E. inversion E. 
      apply (arena_start Y.M Y.lab Y.enab Y.arena) in H. 
      simpl in *. inversion H.
      split. assumption. 
             intros n E1. inversion E1. apply H2 in H5. inversion H5. reflexivity.
  Qed.

  Lemma A_to_Q_ok : A_to_Q M lab enab.
  Proof.
    unfold A_to_Q. intros m n E Eq. inversion E.
      apply (arena_AQ X.M X.lab X.enab X.arena) in H0.      
        rewrite <- H1 in Eq. unfold l_QA in *. simpl in *.
        rewrite (inv_preserves_qa X.M) in *; auto.
      apply (arena_AQ Y.M Y.lab Y.enab Y.arena) in H0.
        rewrite <- H1 in Eq. unfold l_QA in *. simpl in *.
        auto.
      apply (arena_start Y.M Y.lab Y.enab Y.arena) in H1. inversion H1.
        unfold l_QA. simpl. rewrite H3. reflexivity.
  Qed.

  Lemma P_to_O_ok : P_to_O M lab enab.
  Proof.
    unfold P_to_O. intros m n E. unfold not. intro Eq. inversion E.
      apply (arena_PO X.M X.lab X.enab X.arena) in H0. unfold not in H0.
        unfold l_OP in *. rewrite <- H in Eq. rewrite <- H1 in Eq. simpl in Eq.
        apply (inv_bijective_po X.M) in Eq. auto.
      apply (arena_PO Y.M Y.lab Y.enab Y.arena) in H0. unfold not in H0.
        unfold l_OP in *. rewrite <- H in Eq. rewrite <- H1 in Eq. simpl in Eq. auto.
      rewrite <- H in Eq. rewrite <- H2 in Eq. unfold l_OP in Eq. simpl in Eq. 
        apply (arena_start X.M X.lab X.enab X.arena) in H0. inversion H0.
        apply (arena_start Y.M Y.lab Y.enab Y.arena) in H1. inversion H1.
        rewrite H5 in Eq. unfold inv in Eq. rewrite H3 in Eq. simpl in Eq. inversion Eq.
  Qed.

(*
  Lemma unique_justifier_ok : unique_justifier M lab enab.
  Proof. 
    unfold unique_justifier. intros l m n El Em. inversion El. inversion Em. 
      apply (arena_unique_justifier X.M X.lab X.enab X.arena x0) in H0. 
        rewrite H0. reflexivity.
        rewrite <- H1 in H4. inversion H4. rewrite H6 in H3. assumption.
      rewrite <- H4 in H1. inversion H1.
      rewrite <- H1 in H5. inversion H5. rewrite H7 in H3.
        apply (arena_start X.M X.lab X.enab X.arena) in H3. 
        inversion H3. apply H8 in H0. inversion H0.
      rewrite <- H1 in Em. inversion Em. 
        apply (arena_unique_justifier Y.M Y.lab Y.enab Y.arena x0) in H0. 
        rewrite H0. reflexivity. assumption.
      rewrite <- H2 in El. rewrite <- H2 in Em. 
        inversion El. rewrite <- H3 in H. inversion H.
        inversion Em. apply (arena_start X.M X.lab X.enab X.arena) in H5. 
          inversion H5. apply H11 in H9. inversion H9.
  Qed.
*)

  Hint Resolve start_OQ_ok A_to_Q_ok P_to_O_ok (*unique_justifier_ok*).

  Definition arena : arena M lab enab.
  Proof.
    apply mk_arena; split; auto.
  Qed.

End ExpArena.