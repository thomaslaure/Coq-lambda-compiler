Require Import Arith.


(*Partie 1*)

(*1.1 : Définition des termes *)

Inductive term : Set :=
  | var : nat -> term   (*définition des termes*)
  | lambda : term -> term
  | app : term -> term -> term.

(*1.2 Termes clos *)

(*toute variable est liée ou d'indice inférieur strictement à n*)
Fixpoint C (n : nat) (t : term) : Prop := 
  match t with
  | var m => m<n 
  | lambda tp => C (S n) tp (*dans une abstraction, tous les indices sont décalés*)
  | app t1 t2 => (C n t1) /\ (C n t2)
end.

(*un terme est clos si toutes ses variables libres sont d'indice strictement inférieur à 0*)
Definition closed (t : term) : Prop := C 0 t.


Lemma C_transitivity : forall t : term, forall n :nat, (C n t) -> (C (S n) t).
Proof.
 induction t. 
  intros. simpl. apply le_S. apply H.
  intros. simpl. apply ((IHt (S n)) H).
  intros. elim H. intros. simpl. split.
  apply ((IHt1 n) H0). apply ((IHt2 n) H1).
Qed.  

Lemma corollary_C_i : forall t : term, forall i : nat, forall p : nat, 
 C i t -> C (i+p) t.
Proof.
  induction p. intros. rewrite (plus_0_r i). trivial.
  intros. rewrite plus_comm. rewrite Nat.add_succ_l. apply C_transitivity.
  rewrite plus_comm. apply IHp. trivial.
Qed.

(*on démontre immédiatement que si t est clos, pour tout n, C[n](t)*)
Lemma corollary_C : forall t : term, closed t -> forall i : nat, C i t.
Proof.
  intros. induction i. apply H. apply C_transitivity. apply IHi.
Qed.

(*1.3 : substitution*)

(*décale les variables d'indice supérieur à l dans u de p crans, augmente l sous les lambda-abstractions*)
Fixpoint shift ( u : term) (l : nat) (p : nat) : term :=
  match u with
  | var i => if leb l i then var (i+p) else  var i 
  | app u1 u2 => app (shift u1 l p) (shift u2 l p)
  | lambda u1 => lambda (shift u1 (S l) p)
end.

(*renvoie u si i=j=, v sinon, v destiné à être var j*)
Fixpoint subst_var (i : nat) (j : nat) (p : nat) (u : term) (v : term) : term :=
  match i,j with
  | 0,0 => shift u 0 p
  | 0, S m => v 
  | S m, 0 => v
  | S n, S m => subst_var n m p u v
end.

(*substitue u dans t à l'indice i, sachant qu'on a déjà un décalage p*)
Fixpoint subst_par (t : term) (i : nat) (p :nat) (u : term) : term :=
  match t with 
  | var j => subst_var i j p u (var j)
  | app t1 t2 => app (subst_par t1 i p u) (subst_par t2 i p u)
  | lambda t1 => lambda (subst_par t1 (S i) (S p) u)
end.


Definition subst (t : term) (i : nat) (u : term) := subst_par t i 0 u.


Lemma null_shift : forall u : term, forall l : nat, shift u l 0 = u.
Proof.
  induction u. intros. simpl. case_eq (leb l n). rewrite Nat.add_0_r. trivial.
  trivial. intros. simpl. f_equal. apply IHu. intros. simpl. f_equal. apply IHu1.
  apply IHu2.
Qed.

(*preuves du résultat de subst_var*)
Lemma subst_var_eq : forall i : nat, forall j : nat, forall p : nat, forall u : term, 
  forall v : term,
  j=i->subst_var i j p u v= shift u 0 p.
Proof.
  induction i. intros. rewrite H. simpl. trivial.
 intros. rewrite H. simpl. apply IHi. trivial.
Qed.

Lemma subst_var_diff : forall i : nat, forall j : nat, forall p : nat, forall u : term,
  forall v : term, (i<j \/ j<i)-> subst_var i j p u v = v.
Proof.
  induction i. induction j. intros. exfalso. elim H ; simpl ; intros ; apply (lt_0_neq 0) ; trivial ; trivial.
  intros. elim H. intros. simpl. trivial.
 intros. exfalso. apply (le_Sn_0 j). apply lt_le_S. apply (lt_pred j 0). trivial.
  induction j. intros. elim H. intros. exfalso. apply (le_Sn_0 i). apply lt_le_S. apply (lt_pred i 0). trivial.
  intros. simpl. trivial.
  intros. elim H. intros. simpl. apply IHi. left. apply (lt_S_n i j). trivial.
  intros. simpl. apply IHi. right. apply (lt_S_n j i). trivial.
Qed.

(*preuves que la substition dans un terme qui vérifie C[i] le laisse inchangé*)
Lemma closed_subst_par_C : forall t : term, forall i : nat, forall p : nat, forall u : term, 
  C i t -> subst_par t i p u = t.
Proof.
  induction t. intros. simpl. apply subst_var_diff. right. apply H. intros. simpl. f_equal.
  apply IHt. apply H. intros. simpl. f_equal. apply IHt1. apply H. apply IHt2. apply H.
Qed.

Lemma closed_subst_C : 
forall t : term, forall i : nat, (C i t -> forall u : term, (subst t i u = t)).
Proof.
  intros. apply closed_subst_par_C. trivial.
Qed. 

Lemma closed_subst : forall t : term, closed t -> forall i : nat, forall p : nat,
  forall u : term, subst t i u =t.
Proof.
  intros. apply closed_subst_C. apply corollary_C. trivial.
Qed.


(*1.4 : substitution parallèle*)
(*renvoie le j-i ème élément de la liste ou v si cet élément n'existe pas, c'est 
  si v=var j la substitution parallèle de var j par la liste, p est toujours le shift*)
Fixpoint mult_subst_var (i : nat) (j : nat) (p : nat) (l : list term) (v : term) : term :=
  match i,j,l with
  | _,_, nil => v
  | S _, 0, cons t q => v
  | S n, S m, cons t q => mult_subst_var n m p l v
  | 0, 0, cons t q=> shift t 0 p
  | 0, S m, cons t q => mult_subst_var 0 m p q v
end.

(*fait la substitution parallèle dans t en sachant que le shift vaut p*)
Fixpoint mult_subst_par (t : term) (i : nat) (p : nat) (l : list term) : term :=
  match t with 
  | var j => mult_subst_var i j p l (var j)
  | lambda t1 => lambda (mult_subst_par t1 (S i) (S p) l)
  | app t1 t2 => app (mult_subst_par t1 i p l) (mult_subst_par t2 i p l)
end.

Definition mult_subst (t : term) (i : nat) (l : list term) := mult_subst_par t i 0 l.

(*trois lemmes successifs pour démontrer que la substitution par une liste vide ne change pas le terme*)
Lemma m_s_v_nil : forall i : nat, forall j : nat, forall p : nat, forall v : term,
      mult_subst_var i j p nil v = v.
Proof.
  intros. induction i ; induction j ; simpl ; trivial.
Qed.

Lemma m_s_p_nil : forall t : term, forall i : nat, forall p : nat,
    mult_subst_par t i p nil = t.
Proof.
  induction t. intros. apply m_s_v_nil. 
  intros. simpl. f_equal. apply IHt.
  intros. simpl. f_equal. apply IHt1. apply IHt2.
Qed.

Lemma mult_subst_nil : forall t : term, forall i : nat, mult_subst t i nil = t.
Proof.
  intros. apply m_s_p_nil.
Qed.


(*trois lemmes successifs pour démontrer que la substitution parallèle par une liste d'un terme 
  correspond à la substitution unaire définie précédemment*)
Lemma m_s_v_un : forall i : nat, forall j : nat, forall p : nat, 
  forall u : term, forall v : term,
  mult_subst_var i j p (cons u nil) v = subst_var i j p u v.
Proof.
  induction i. induction j. intros. simpl. trivial. intros. simpl. apply m_s_v_nil.
  induction j. intros. simpl. trivial.
  intros. simpl. apply IHi.
Qed.

Lemma m_s_p_un : forall t : term, forall i : nat, forall p : nat, forall u : term, 
  C i t -> mult_subst_par t i p (cons u nil) = t.
Proof.
  induction t. intros. simpl. apply (eq_ind (subst_var i n p u (var n))). apply m_s_v_un. apply subst_var_diff.
  right. apply H.
  intros. simpl. f_equal. apply (IHt (S i)). apply H.
  intros. simpl. f_equal. apply IHt1. apply H. apply IHt2. apply H.
Qed.

Lemma mult_subst_un : forall t : term, forall i : nat, forall u : term, 
  C i t -> mult_subst t i (cons u nil) = t.
Proof.
  intros. apply m_s_p_un. apply H.
Qed.


(*on arrive à la démonstration principale de la partie, qu'on va faire par étapes*)
(*prédicat : tous les éléments de l vérifient C[i]*)
Fixpoint C_l  (i : nat) (l : list term) : Prop :=
  match l with
  | nil => True
  | cons u q => (C i u) /\ (C_l i q)
end.

(*démontre que si un terme vérifie C[i] et qu'on le shifte de p rangs, il vérifie C[i+p]*)
Lemma closed_post_shift : forall u : term, forall i : nat, forall p : nat, forall l : nat,
  C i u -> C (i+p) (shift u l p).
Proof.
  induction u. intros. simpl. case_eq (leb l n). intros. simpl. apply (plus_lt_compat_r n i p). apply H.
  intros. simpl. apply (lt_plus_trans n i p). apply H.
  intros. simpl. apply (IHu (S i)  p (S l)). apply H.
  intros. simpl. split. apply IHu1. apply H. apply IHu2. apply H.
Qed.


(*lemme très utile : un terme qui vérifie C[i] ou qui est une variable j différente de i
  n'est pas modifié par la substitution*)
Lemma closed_or_unreachable : forall i : nat, forall t : term, forall u : term, forall p : nat,
  (C i t)\/(exists j : nat, t= var j /\ (i < j \/ i > j)) -> subst_par t i p u = t.
Proof.
  intros. elim H. intros. apply closed_subst_par_C. trivial.
  intros. elim H0. intros. elim H1. intros. rewrite H2. simpl. apply subst_var_diff. 
  apply H3.
Qed.

(*prédicat : t est un élément de la liste l*)
Fixpoint belongs (t : term) (l : list term) : Prop :=
  match l with
  | nil => False
  | cons u q => t = u \/ belongs t q
  end.

(*prédicat : t est le shifté de p rangs d'un élément de l*)
Fixpoint belongs_shift (t : term) (l : list term) (lim : nat) (p : nat) :=
  match l with
  | nil => False
  | cons u q => t = shift u lim p \/ belongs_shift t q lim p
end.

(*simple réciproque de la définition de C_l : si t apparaît dans l et C_l[i](t), alors C[i](t)*)
Lemma C_recip : forall t : term, forall l : list term, forall i : nat,
  belongs t l -> C_l i l -> C i t.
Proof.
  induction l. intros. exfalso. apply H.
  intros. elim H. intros. rewrite H1. apply H0.
  intros. apply IHl. apply H1. apply H0.
Qed.

Lemma C_l_trans : forall l : list term, forall i : nat, forall p : nat,
  C_l i l -> C_l (i+p) l.
Proof.
  induction l. intros. simpl.  trivial.
  intros. simpl. split. apply corollary_C_i. apply H. apply IHl. apply H.
Qed.

(*si t est le shifté d'un élément de l, que tous les éléments de l vérifient C[i],
t vérifie C[i+p]*)
Lemma C_recip_shift : forall t : term, forall l : list term, forall lim : nat, forall p : nat,
  forall i : nat,
  C_l i l -> belongs_shift t l lim p -> C (i+p) t.
Proof.
  induction l. intros. exfalso. apply H0.
  intros. elim H0. intros. rewrite H1. apply closed_post_shift. apply H.
  apply IHl. apply H.
Qed.



(*4 lemmes évidents sur le résultat de mult_subst_var 
(substitution parallèle d'une variable) rendront la démonstration de 4) plus facile*)
(*le résultat de mult_subst_par est soit un élément de l shifté, soit v*)
Lemma int_0 : forall v : term, forall l : list term, forall i : nat, forall j : nat, 
  forall p : nat,
  belongs_shift (mult_subst_var i j p l v) l 0 p  \/ mult_subst_var i j p l v = v.
Proof.
  induction l. intros. right. apply m_s_v_nil.
  induction i. induction j. intros. left. simpl. left. trivial.
  intros. simpl. elim (IHl 0 j p). intros. left. right. trivial.
  intros. right. trivial.
  induction j. intros. simpl. right. trivial.
  simpl. intros. elim (IHi j p). intros. elim H. intros. 
  left. left. trivial. intros. left. right. trivial.
  intros. right. trivial.
Qed.

(*si j<i, on renvoie bien v*)
Lemma int_1 : forall v : term, forall l : list term, forall i : nat, forall j : nat,
  forall p : nat,
  j<i -> mult_subst_var i j p l v = v.
Proof.
  induction i. induction j. intros. exfalso. apply (lt_irrefl 0 H).
   intros. exfalso. apply (le_Sn_0 (S j)). apply (lt_le_S (S j) 0). trivial.
  induction j. intros. simpl. induction l. trivial. trivial.
  intros. simpl. induction l. trivial.
  apply IHi. apply lt_S_n. trivial.
Qed.


(*si j=i, on renvoie bien le premier élément de la liste shifté, et si on applique à la queue de la 
liste et à S i, on renvoie bien v*)
Lemma int_2 : forall v : term, forall q : list term, forall u : term, forall i : nat, 
  forall j : nat, forall p : nat, j=i -> (mult_subst_var i j p (cons u q) v = shift u 0 p /\ 
      mult_subst_var (S i) j p q v = v).
Proof.
  induction i. intros. rewrite H. split. simpl. trivial.
   apply int_1. apply neq_0_lt. trivial.
  intros. rewrite H. split. apply IHi. trivial. apply int_1. apply lt_n_Sn.
Qed.

(*si j>i, alors on substitue bien dans la queue de la liste*)
Lemma int_3 : forall v : term, forall q : list term, forall u : term, forall i : nat,
  forall j : nat, forall p : nat,
   j>i -> mult_subst_var i j p (cons u q) v = mult_subst_var (S i) j p q v.
Proof.
  induction i. induction j. intros. exfalso. apply (lt_irrefl 0). trivial.
  intros. simpl. induction q. apply m_s_v_nil. trivial.
  induction j. intros. exfalso. apply (le_Sn_0 (S i)). apply (lt_le_S (S i) 0). trivial.
  intros. simpl. induction q. apply (eq_ind (mult_subst_var (S i) j p nil v)).
  apply IHi. apply lt_S_n. trivial. apply m_s_v_nil.
  apply IHi. apply lt_S_n. trivial.
Qed.


(*pour conclure, on va avoir besoin de ne pas shifter le i tel que C_l i q et c'est 
    pour cela que l'on va travailler avec des i+p, i.e. la queue de la liste vérifie C[i]
  mais on substitue récursivement à l'indice i+p (et initialement dans la substitution p 
  vaudra 0*)

(*on raisonne par disjonction de cas sur la position relative de i+p
  (indice de substitution),et j pour prouver que la substitution parallèle de var j vérifie 
  bien ce que l'on veut*)
Lemma m_s_v_succ : forall i : nat, forall j : nat, forall u : term, forall q : list term,
  forall p : nat,
    C_l i q -> mult_subst_var (i+p) j p (cons u q) (var j) = 
    subst_par (mult_subst_var (S (i+p)) j p q (var j)) (i+p) p u.
Proof.
  intros. elim (le_or_lt j (i+p)). intros. elim (le_lt_or_eq j (i+p)). intros. apply (eq_ind (var j)).
  apply int_1. trivial. apply eq_sym. apply (eq_ind (mult_subst_var (S (i+p)) j p q (var j))).
  apply closed_or_unreachable. right. exists j. split. apply int_1. apply lt_S. trivial.
  right. trivial.
  apply int_1. apply lt_S. trivial.
  intros. apply (eq_ind (shift u 0 p)). apply int_2. trivial.
  apply (eq_ind (subst_par (var (i+p)) (i+p) p u)). simpl. apply eq_sym.
  apply subst_var_eq. trivial. 
  f_equal. rewrite H1. apply eq_sym. apply int_2. trivial. trivial. trivial.
  intros. apply (eq_ind (mult_subst_var (S (i+p)) j p q (var j))). apply int_3. trivial.
  apply eq_sym. apply closed_or_unreachable. elim (int_0 (var j) q (S (i+p)) j p).
  intros. left. apply (C_recip_shift (mult_subst_var (S (i+p)) j p q (var j)) q 0 p i).
  trivial. trivial.
  intros. right. exists j. split. trivial. left. apply H0.
Qed. 

(* avec le lemme précédent, l'induction est triviale pour t quelconque*)
Lemma m_s_p_succ : forall t : term, forall q : list term, forall i : nat, 
  forall u : term, forall p : nat,
    C_l i q -> mult_subst_par t (i+p) p (cons u q) = 
              subst_par (mult_subst_par t (S (i+p)) p q) (i+p) p u.
Proof.
  induction t. intros. simpl. apply m_s_v_succ. trivial.
  intros. simpl. f_equal. rewrite <- Nat.add_succ_l. rewrite plus_Snm_nSm. apply IHt. trivial.
  intros. simpl. f_equal. apply IHt1. trivial. apply IHt2. trivial.
Qed.

(*application du lemme précédent pour p=0, sert pour l'unification dans le lemme suivant*)
Lemma m_s_p_succ_0 :forall t : term, forall q : list term, forall i : nat, 
  forall u : term, 
  C_l i q -> mult_subst_par t i 0 (cons u q) = 
              subst_par (mult_subst_par t (S i) 0 q) i 0 u.
Proof.
  intros. rewrite <- (Nat.add_0_l i). rewrite plus_comm. apply (m_s_p_succ t q i u 0). trivial.
Qed.


(*lemme principal de la partie*)
Lemma mult_subst_succ : forall t : term, forall q : list term, forall i : nat, 
  forall u : term,
    C_l i q -> mult_subst t i (cons u q) = subst (mult_subst t (S i) q) i u.
Proof.
  intros. apply m_s_p_succ_0. trivial.
Qed.



(* Partie 2*)

(*2.1 : Substitution*)
(*définit si u_1 u_2 est un rédex et le cas échéant si v en est la contraction*)
Definition redexes (u1 : term) (u2 : term) (v : term) : Prop :=
  match u1 with
  | lambda u3 => v = subst u3 0 u2 (*v=u_3[0<-u_2]*)
  | _ => False
end.

(*prédicat u -> v*)
Fixpoint reducts (u : term) (v : term) : Prop :=
  match u with
  | app u1 u2 => (redexes u1 u2 v) \/ 
                  (match v with 
                  | app v1 v2 =>
                  ((reducts u1 v1)/\(u2=v2))\/((u1=v1)/\(reducts u2 v2))
                (*soit u_1 u_2 est le rédex contracté, soit la réduction se fait d'un côté de l'application*)
                  | _ => False 
                  end )(*nécessairement u_1 u_2 doit être le rédex contracté*)
  | lambda u1 => match v with 
              | lambda v1 =>  reducts u1 v1 (*deux lambda-abstractions se réduisent l'une en l'autre*)
              | _  => False 
                end
  | _ => False 
  
end.


(*2.2 : Cloture réflexive et transitive de la substitution*)
(*prédicat : u->*v en n étapes*)
Fixpoint reducts_star_n (u : term) (v :term) (n : nat) : Prop :=
  match n with
  | 0 => u=v
  | S m => exists t : term, reducts u t /\ reducts_star_n t v m
end.

(*u->*v en un nombre quelconque d'étapes*)
Definition reducts_star ( u :term)  (v : term) : Prop :=
  exists n : nat, reducts_star_n u v n.


(*prouve que u->*u qui n'apparaît pas dans la définition de reduct_star mais dans reduct_star_n 0*)
Lemma reflex : forall u : term, reducts_star u u.
Proof.
  intros. exists 0. simpl. trivial.
Qed.

(*2.3 Clôture par contexte*)
(*on prouve ensuite les lemmes de clôture d'abord par induction sur le nombre d'étapes en montrant que c'est le même
  puis sur ->* immédiatement*)
Lemma closure_lambda_n : forall n : nat,
  forall u : term, forall v : term,
   reducts_star_n u v n -> reducts_star_n (lambda u) (lambda v) n.
Proof.
  induction n. intros. simpl. f_equal. apply H. intros. elim H. intros.
  exists (lambda x). split. simpl. apply H0. apply IHn. apply H0.
Qed.

Lemma closure_lambda : forall u : term, forall v : term,
  reducts_star u v -> reducts_star (lambda u) (lambda v).
Proof.
  intros. elim H. intros. exists x. apply closure_lambda_n. trivial.
Qed.

Lemma closure_left_n : forall n : nat, forall u1 : term, forall u2 : term, forall v : term,
  reducts_star_n u1 u2 n -> reducts_star_n (app u1 v) (app u2 v) n.
Proof.
  induction n. intros. simpl. f_equal. apply H.
  intros. elim H. intros. exists (app x v). split.
  simpl. right. left. split. apply H0. trivial. apply IHn. apply H0.
Qed.

Lemma closure_left : forall u1 : term, forall u2 : term, forall v : term,
  reducts_star u1 u2 -> reducts_star (app u1 v) (app u2 v).
Proof.
  intros. elim H. intros. exists x. apply closure_left_n. trivial.
Qed.

Lemma closure_right_n : forall n : nat, forall u1 : term, forall u2 : term, forall v : term,
  reducts_star_n u1 u2 n -> reducts_star_n (app v u1) (app v u2) n.
Proof.
  induction n. intros. simpl. f_equal. apply H.
  intros. elim H. intros. exists (app v x). split. simpl.
   right. right. split. trivial. apply H0.
  apply IHn. apply H0.
Qed.

Lemma closure_right : forall u1 : term, forall u2 : term, forall v : term,
  reducts_star u1 u2 -> reducts_star (app v u1) (app v u2).
Proof.
  intros. elim H. intros. exists x. apply closure_right_n. trivial.
Qed.



 
(*Partie 3*)
(*3.2 : Définition des états*)
Inductive code : Set := 
  | access : nat -> code
  | grab : code -> code
  | push : code -> code -> code.

Inductive env : Set :=
  | nillenv : env
  | couple : code -> env -> env -> env.

Inductive stack : Set := 
  | nillstack : stack
  | const : code -> env -> stack -> stack.

Inductive state : Set :=
  stat : code -> env -> stack -> state.

(*3.3 Sémantique de la machine de Krivine*)
Definition semantics (s : state) : option state :=
  match s with 
  | stat (access 0)  (couple c0 e0 e) s => Some (stat c0 e0 s)
  | stat (access 0)  nillenv  s  => None
  | stat (access (S m)) (couple c0 e0 e) s => Some (stat (access m) e s)
  | stat (access (S m)) nillenv s => None
  | stat (grab c) e (const c0 e0 s) => Some (stat c (couple c0 e0 e) s)
  | stat (grab c) e nillstack => None
  | stat (push c1 c) e s => Some (stat c e (const c1 e s))
end.


          

(*Partie 4*)
(*4.1 : Compilation*)
Fixpoint compile (t : term) : code :=
  match t with
  | var n => access n
  | app v u => push (compile u) (compile v)
  | lambda u => grab (compile u)
end.

(*Partie 5*)
(*5.1 : Définition de tau*)

Fixpoint tau_code (c : code) : term :=
  match c with
  | access n => var n
  | push c1 c2 => app (tau_code c2) (tau_code c1)
  | grab c1 => lambda (tau_code c1)
end.

(*Renvoie une liste de termes u0...un telle que tau(e) = [0<- u0...un]*)
Fixpoint tau_env (e : env) : list term :=
  match e with
  | nillenv => nil
  | couple c0 e0 e1 => cons (mult_subst (tau_code c0) 0 (tau_env e0)) (tau_env e1)
end.

(*On utilise un accumulateur pour tenir compte de l'associativité de l'application*)
Fixpoint tau_acc (u : term ) (s : stack) : term :=
  match s with 
  | nillstack => u
  | const c e q => tau_acc (app u (mult_subst (tau_code c) 0 (tau_env e))) q
end.

Definition tau (s :state) : term :=
  match s with 
  | stat c e st => tau_acc (mult_subst (tau_code c) 0 (tau_env e)) st
end.

(*5.2 : tau (compile t) = t*)
Lemma compose: forall t : term, tau_code (compile t) = t.
Proof.
  induction t. simpl. trivial.
  simpl. apply (eq_ind (lambda t)). f_equal. apply IHt. trivial.
  simpl. apply (eq_ind (app t1 t2)). f_equal. apply IHt1. apply IHt2.
  trivial.
Qed.


(*5.3 *)
(*Définition des états corrects*)

Fixpoint length_e (e : env) : nat :=
  match e with 
  | nillenv => 0
  | couple c e1 e2 => S (length_e e2)
end.


Fixpoint correct_e (e : env) : Prop :=
  match e with
  | nillenv => True
  | couple c e0 e1 => (correct_e e0)/\(correct_e  e1)/\
                                        (C (length_e e0) (tau_code c))
end.


Fixpoint correct_s (s : stack) : Prop :=
  match s with 
  | nillstack => True
  | const c e q => (correct_s q)/\ (correct_e e)/\(C (length_e e) (tau_code c))
end.

Definition correct (s : state ) : Prop :=
  match s with 
  | stat c e st => (correct_e e)/\ (correct_s st)/\(C (length_e e) (tau_code c))
end.

Definition correct_o (s : option state) : Prop :=
  match s with
  | None => True
  | Some t => correct t
end.

(* une transition à partir d'un état correct mène à None où à un état correct*)
Lemma correct_trans : forall s1 : state,
   correct s1 -> correct_o (semantics s1).
Proof.
  intros. induction s1. induction c. induction e. induction s. simpl. induction n ; simpl ; trivial.
  induction n. simpl. trivial. simpl. trivial. induction n. simpl. split.
  apply H. split. apply H. apply H. simpl. split. apply H. split. apply H.
  apply lt_S_n. apply H.
  induction e. induction s. simpl. trivial. simpl. split. split. apply H. split. trivial.
  apply H. split. apply H. apply H.
  induction s. simpl. trivial. simpl. split. split. apply H. split. split.
  apply H. split. apply H. apply H. apply H. split. apply H. apply H.
  simpl. split. apply H. split. split. apply H. split. apply H. apply H. apply H.
Qed.
  

(*4*)
(*On va faire une série de lemmes intermédiaires pour aboutir au résultat*)

Fixpoint length_l (l : list term) : nat :=  
  match l with 
  | nil => 0
  | cons u q => S (length_l q)
end.

(*prouve que si une variable est d'indice plus petit que la longueur de la liste, alors 
  décrémenter  la variable et l'indice de départ mène à la même chose, ceci car la 
  substitution parallèle sélectionne le même terme de la liste*)
Lemma var_dec_n : forall l : list term, forall n : nat, forall i : nat, n < length_l l -> 
  mult_subst (var (n+ S i)) (S i) l = mult_subst (var (n+i)) i l. 
Proof.
  induction l. intros. exfalso. apply (lt_n_0 n). apply H.
  induction n. intros. apply (eq_ind (shift a 0 0)). apply int_2. trivial.
  apply eq_sym. apply int_2. trivial.
  intros. apply (eq_ind (mult_subst (var (S n + i)) (S i) l)).
  apply (eq_ind (mult_subst (var (S n + S i)) (S (S i)) l)).
  apply int_3. apply (plus_lt_compat_r 0 (S n) (S i)). apply lt_0_Sn.
  rewrite (plus_Snm_nSm). rewrite (plus_Snm_nSm n i). apply (IHl n (S i)).
  apply lt_S_n. apply H.
  apply eq_sym. apply int_3. apply (plus_lt_compat_r 0 (S n) i). apply lt_0_Sn.
Qed.

(*prouve que sous la même hypothèse, on peut décrémenter la variable et supprimer le 
  premier terme de la liste*)
Lemma var_subst_n : forall l : list term, forall n : nat, forall u : term, 
  n < length_l l -> mult_subst (var (S n)) 0 (cons u l) = mult_subst (var n) 0 l.
Proof.
  intros. apply (eq_ind (mult_subst (var (S n)) 1 l)). apply int_3. apply lt_0_Sn.
  rewrite <- (Nat.add_0_r n). rewrite <- Nat.add_succ_r. apply var_dec_n. trivial.
Qed.

(*c'est évident mais utile, la longueur de la liste des termes tau_env e est la même 
  que la longueur de e*)
Lemma equals_lenghts_e : forall e : env, length_e e = length_l (tau_env e).
Proof.
  induction e. simpl. trivial. simpl. f_equal. apply IHe2.
Qed.

(*on peut maintenant prouver la propriété voulue pour les 3 transitions où il ne se passe 
  rien : pour access n, access 0 et push, les tau de chaque côté des transitions coïncident*)
Lemma correct_red_Sn : forall n : nat, forall e : env, forall c0 : code, forall e0 :env, forall s : stack,
  correct (stat (access (S n)) (couple c0 e0 e) s) -> 
    tau (stat (access (S n)) (couple c0 e0 e) s) = tau (stat (access n)  e s).
Proof.
  induction s. simpl. intros. apply var_subst_n. apply lt_S_n. rewrite <- equals_lenghts_e. 
  apply H. intros. simpl. f_equal. f_equal. apply var_subst_n. rewrite <- equals_lenghts_e. 
  apply lt_S_n. apply H.
Qed.


Lemma correct_red_0 : forall e : env, forall c0 : code, forall e0 :env, forall s : stack,
    tau (stat (access 0) (couple c0 e0 e) s) = tau (stat c0 e0 s).
Proof.
  induction s. intros. simpl. apply (eq_ind (shift (mult_subst (tau_code c0) 0 (tau_env e0)) 0 0)).
  apply int_2. trivial. apply null_shift.
  intros. simpl. f_equal. f_equal. apply (eq_ind (shift (mult_subst (tau_code c0) 0 (tau_env e0)) 0 0)).
  apply int_2. trivial. apply null_shift.
Qed.


Lemma correct_red_push : forall c : code, forall c' : code, forall e : env, forall s : stack,
  tau (stat (push c' c) e s) = tau (stat c e (const c' e s)).
Proof.
  induction s. intros. simpl. trivial. simpl. f_equal.
Qed.


(*pour grab, il va falloir faire un peu plus de travail*)

(*corollaire de int_2 (avec mult_subst_var) mais quand t est directement la variable var i*)
Lemma int_2_prime : forall i : nat, forall u : term, forall l : list term, 
  mult_subst (var i) i (cons u l) = u.
Proof.
  intros. apply (eq_ind (mult_subst_var i i 0 (cons u l) (var i))).
  simpl. trivial. apply (eq_ind (shift u 0 0)). apply int_2. trivial. apply null_shift.
Qed. 


(*prouve que si un terme vérifie C i, alors shifter ses variables d'indice supérieur 
  à i ne change rien (car ces variables n'existent pas)*)
Lemma shift_simpl : forall p : nat, forall t : term, forall i : nat, C i t -> 
        shift t i p = t.
Proof.
  induction t. intros. simpl. case_eq (leb i n).  intros. exfalso. apply (le_not_lt i n).
  apply (leb_complete i n). trivial. apply H. intros. trivial. intros. simpl. 
  f_equal. apply IHt. apply H. intros. simpl. f_equal. apply IHt1. apply H. apply IHt2. apply H.
Qed. 

(*prouve que si une liste ne contient que des termes clos, alors la substitution parallèle
  avec un shift quelconque équivaut à le faire avec un shift nul (car on ne shifte que les termes de la liste,
  et puisqu'ils sont clos cela ne change rien d'après le lemme précédent)*)
Lemma mult_shift_simpl : forall l : list term, forall t : term, forall i : nat, forall p : nat, 
  C_l 0 l -> mult_subst_par t i p l = mult_subst_par t i 0 l.
Proof.
  induction l. intros. apply (eq_ind t). apply m_s_p_nil. apply eq_sym. apply m_s_p_nil.
  induction t. intros. elim (le_or_lt n i). intros. elim (le_lt_or_eq n i). intros.
  apply (eq_ind (var n)). apply int_1.  trivial. apply eq_sym. apply int_1. trivial.
  intros. rewrite H1.  apply (eq_ind a). apply (eq_ind (shift a 0 p)).
  apply int_2. trivial. apply shift_simpl. apply H. apply eq_sym. apply (eq_ind (shift a 0 0)).
  apply int_2. trivial. apply null_shift. trivial. intros. simpl. 
  rewrite (int_3 (var n) l a i n p). rewrite (int_3 (var n) l a i n 0). apply (IHl (var n) (S i) p). apply H.
  trivial. trivial. intros. simpl. f_equal. apply (eq_ind (mult_subst_par t (S i) 0 (cons a l))).
   apply (IHt (S i) (S p)). trivial. apply eq_sym. apply (IHt (S i) 1). trivial.
  intros. simpl. f_equal. apply IHt1. trivial. apply IHt2. trivial.
Qed.

(*corollaires de int_1 et int_3 quand t est var j, évidents mais coq refuse d'appliquer 
  directement int_1 et int_3*)
Lemma int_1_prime : forall i : nat, forall j : nat, forall l : list term, 
  j < i -> mult_subst (var j) i l = var j.
Proof.
  intros. simpl. apply int_1. trivial.
Qed.

Lemma int_3_prime : forall i : nat, forall j : nat, forall l : list term, forall u : term, 
  j>i -> mult_subst (var j) i (cons u l) = mult_subst (var j) (S i) l.
Proof.
  intros. apply int_3. trivial.
Qed.

(*prouve que si un terme est le shifté de 0 rangs d'un élément de l, alors il appartient à l*)
Lemma null_shift_l : forall l : list term, forall t : term, belongs_shift t l 0 0 -> belongs t l.
Proof.
  induction l. intros. simpl. apply H. intros. elim H. intros. simpl. left.
  rewrite <- (null_shift a 0). trivial. intros. simpl. right. apply IHl. trivial.
Qed.

(*dernier corollaire d'un int_i*)
Lemma int_0_prime : forall i : nat, forall j : nat, forall l : list term, 
  belongs (mult_subst (var j) i l) l \/ mult_subst (var j) i l = var j.
Proof.
  intros. elim (int_0 (var j) l i j 0). intros. left. apply null_shift_l. apply H.
  intros. right. apply H.
Qed.

(*dans le même esprit que les int_i, prouve dans quel cas on sélectionne un élément
  de la liste en le shiftant, puis on écrit encore son corollaire*)
Lemma int_4 : forall v : term, forall l : list term, forall i : nat, forall j : nat, 
  forall p : nat, i<= j -> j < (i + (length_l l)) -> belongs_shift (mult_subst_var i j p l v) l 0 p.
Proof.
  induction l. intros. exfalso. apply (le_not_lt i j). apply H. rewrite <- (Nat.add_0_r i). apply H0.
  intros. elim (le_lt_or_eq i j). intros. rewrite int_3. simpl. right. apply (IHl (S i) j p).  apply H1. 
  rewrite plus_Snm_nSm. apply H0. apply H1. intros. simpl. left. apply int_2. apply eq_sym. trivial. trivial.
Qed.

Lemma int_4_prime : forall i : nat, forall j : nat, forall l :list term, 
   i<= j -> j < (i + (length_l l)) -> belongs (mult_subst (var j) i l) l.
Proof.
  intros. apply null_shift_l. apply int_4. trivial. trivial.
Qed.

(*si t vérifie C (i + len l) et qu'on remplace toutes les variables d'indice entre i et 
  i+len l par des termes clos, alors le résultat vérifie C i*)
Lemma by_closed : forall t : term, forall l : list term, forall i : nat,
    C_l 0 l -> C (i+ (length_l l)) t -> C i (mult_subst t i l).
Proof.
  induction t. intros. elim (le_or_lt i n). intros. apply corollary_C. 
  apply (C_recip (mult_subst (var n) i l) l 0). apply int_4_prime. trivial. trivial. trivial.
  intros. rewrite int_1_prime. apply H1. trivial.
  intros. simpl. rewrite mult_shift_simpl. apply IHt. trivial. apply H0. trivial.
  intros. simpl. split. apply IHt1. trivial. apply H0. apply IHt2. trivial. apply H0.
Qed. 
    
(*propriété fondamentale pour la suite : tau_env e ne renvoie que des termes clos*)
Lemma closed_env : forall e : env, correct_e e -> C_l 0 (tau_env e).
Proof.
  induction e. intros. simpl. trivial.
  intros. simpl. split. apply by_closed. apply IHe1. apply H. rewrite Nat.add_0_l.
  rewrite <- equals_lenghts_e. apply H. apply IHe2. apply H.
Qed.

(*on peut maintenant prouver que pour un grab, si s est vide, alors on fait exactement
  la réduction d'un rédex*)
Lemma redexes_grab : forall c : code, forall e : env, forall c0 : code, forall e0 : env, forall s : stack, 
  correct (stat (grab c) e (const c0 e0 s)) -> 
  redexes (mult_subst (tau_code (grab c)) 0 (tau_env e)) (mult_subst (tau_code c0) 0 (tau_env e0)) 
      (mult_subst (tau_code c) 0 (cons (mult_subst (tau_code c0) 0 (tau_env e0)) (tau_env e))).
Proof.
  intros. simpl. rewrite mult_shift_simpl. apply mult_subst_succ. apply closed_env. apply H.
  apply closed_env. apply H.
Qed.

(*sert pour l'induction à cause de l'accumulateur, car on fait une réduction tout en bas à gauche*)
Lemma red_trans_acc : forall s : stack, forall t1 : term, forall t2 : term, 
  reducts t1 t2 -> reducts (tau_acc t1 s) (tau_acc t2 s).
Proof.
  induction s. intros. apply H.
  intros. simpl. apply IHs. simpl. right. left. split. trivial. trivial.
Qed.
  

(*on démontre enfin que la transition du grab fait une beta-réduction*)
Lemma correct_red_grab : forall c : code, forall e : env, forall c0 : code,
 forall e0 : env, forall s : stack, 
  correct (stat (grab c) e (const c0 e0 s)) -> reducts (tau (stat (grab c) e (const c0 e0 s)))
        (tau (stat c (couple c0 e0 e) s)).
Proof.
  intros. simpl. apply red_trans_acc. simpl. left. apply (redexes_grab c e c0 e0 s). apply H.
Qed.

(*prédicat : si s2 existe, alors soit les deux états sont égaux, soit ils se beta-réduisent*)
Definition red_equals_o (s1 : state) (s2 : option state) : Prop :=
  match s2 with
  | None => True
  | Some s => reducts (tau s1) (tau s) \/ tau s1 = tau s
end.


(*on prouve enfin qu'une transition à partir d'un état correct mène soit à None,
  soit à un état qui est modulo tau identique ou un réduit*)
Lemma correct_red : forall s : state, correct s -> red_equals_o s (semantics s).
Proof.
  intros. induction s. induction c. induction e. simpl. induction n ; simpl ; trivial.
  induction n. simpl. right. apply correct_red_0. simpl. right. apply correct_red_Sn. apply H.
  induction s. simpl. trivial. simpl. left. apply correct_red_grab. apply H.
  simpl.  right.  apply correct_red_push.
Qed.


(*1.5*)
(*on a travaillé avec les options pour que coq fasse les calculs plus facilement,
  on va maintenant les éliminer et travailler avec des prédicats de réduction*)
Definition reducts_sem (s1 : state) (s2 : state) : Prop :=
  semantics s1 = Some s2.

Lemma elim_option : forall s : state, correct_o (Some s) -> correct s.
Proof.
  intros. apply H.
Qed.

Lemma correct_trans_1 : forall s1 : state, forall s2 : state, correct s1 -> reducts_sem s1 s2 ->
  correct s2.
Proof.
  intros. apply elim_option. rewrite <- H0. apply correct_trans. trivial.
Qed.

Lemma elim_option_bis : forall s1 : state, forall s2 : state, red_equals_o s1 (Some s2) -> (reducts (tau s1) (tau s2)
    \/ tau s1 = tau s2).
Proof.
  intros. apply H. 
Qed.

Lemma correct_red_1 : forall s1 : state, forall s2 : state, correct s1 -> reducts_sem s1 s2 -> 
  (reducts (tau s1) (tau s2) \/ tau s1 = tau s2).
Proof.
  intros. apply elim_option_bis. rewrite <- H0. apply correct_red. trivial.
Qed.

(*l'état est bloqué*)
Definition blocked (s : state) : Prop := semantics s = None.
(* on définit la réduction en n étapes par la machine et on passe par induction les 
  propriétés précédentes*)
Fixpoint reducts_sem_star_n (n : nat) (s1 : state) (s2 : state) : Prop :=
  match n with 
  | 0 => s1 = s2 
  | S m => exists s : state, reducts_sem s1 s /\ reducts_sem_star_n m s s2
end.

Definition reducts_sem_star (s1 : state) (s2 : state) : Prop :=
  exists n : nat, reducts_sem_star_n n s1 s2.


Lemma correct_red_star_n : forall n : nat, forall s1 : state, forall s2 : state, correct s1 ->
  reducts_sem_star_n n s1 s2 -> (correct s2 /\ reducts_star (tau s1) (tau s2)).
Proof. 
  induction n. intros. elim H0. split. trivial. apply reflex.
  intros. elim H0. intros. split. apply (IHn x s2). apply (correct_trans_1 s1 x). 
  trivial. apply H1. apply H1. elim (IHn x s2). intros. elim H3. intros.
  elim (correct_red_1 s1 x). intros.
  exists (S x0). exists (tau x). split. trivial. trivial.
  intros. rewrite H5. trivial. trivial. apply H1. apply (correct_trans_1 s1 x). trivial. apply H1. apply H1.
Qed.

Lemma correct_red_star : forall s1 : state, forall s2 : state, correct s1 -> reducts_sem_star s1 s2 ->
  (correct s2 /\ reducts_star (tau s1) (tau s2)).
Proof.
  intros. elim H0. intros. apply (correct_red_star_n x s1 s2). trivial. trivial.
Qed.

(*concaténation à droites des réductions, car la définition est à gauche*)
Lemma right_trans : forall n : nat, forall t1 : term, forall t2 : term, forall t3 : term,
  reducts_star_n t1 t2 n -> reducts t2 t3 -> reducts_star_n t1 t3 (S n).
Proof.
  induction n. intros. rewrite H. exists t3. split. trivial. simpl. trivial.
  intros. elim H. intros. exists x. split. apply H1. apply (IHn x t2 t3). apply H1. trivial.
Qed.

Lemma right_trans_sem : forall n : nat, forall s1 : state, forall s2 : state, forall s3 : state, 
  reducts_sem_star_n n s1 s2 -> reducts_sem s2 s3 -> reducts_sem_star_n (S n) s1 s3.
Proof.
  induction n. intros. rewrite H. exists s3. split. trivial. simpl. trivial.
  intros. elim H. intros. exists x. split. apply H1. apply (IHn x s2 s3). apply H1. trivial.
Qed.

Lemma complete_option : forall o : option state, o = None \/ (exists s : state, o = Some s).
Proof.
  induction o. right.  exists a. trivial. left. trivial.
Qed.

(*tout état est soit bloquant, soit suivi d'une transition*)
Lemma complete_trans : forall s : state, blocked s \/ (exists s1 : state, reducts_sem s s1).
Proof.
  intros. elim (complete_option (semantics s)). intros. left. apply H.
  intros. right. elim H. intros. exists x. apply H0.
Qed.

(*pour tout n, soit on atteint un état bloquant en moins de n étapes, soit on peut continuer
  au moins une étape de plus*)
Lemma successor_n : forall s : state, forall n : nat, (exists p : nat, exists s1 : state,
    p<= n /\ reducts_sem_star_n p s s1 /\ blocked s1) \/ (exists s1 : state, exists s2 : state,
    reducts_sem_star_n n s s1 /\ reducts_sem s1 s2).
Proof.
  induction n. intros. elim (complete_trans s). intros. left. exists 0. exists s.
  split. apply (le_refl 0). split. simpl. trivial. trivial. intros. right. exists s. elim H. intros. exists x.
  split. simpl. trivial. trivial.
  intros. elim IHn. intros. elim H. intros. elim H0. intros. left. exists x. exists x0.
  split. apply (le_trans x n (S n)). apply H1. apply le_n_Sn. apply H1.
  intros. elim H. intros. elim H0. intros. elim (complete_trans x0).
  intros. left. exists (S n). exists x0. split. trivial. split. apply (right_trans_sem n s x x0).
  apply H1. apply H1. trivial. intros. right. elim H2. intros. exists x0. exists x1.
  split. apply (right_trans_sem n s x x0). apply H1. apply H1. trivial.
Qed.

(* on termine par prouver que l'état (compile t, [],[]) est correct et correspond bien à t via tau*) 
Definition init_stat (t : term) : state := stat (compile t) nillenv nillstack.

Lemma correct_init : forall t : term, closed t -> 
    correct (init_stat t).
Proof.
  intros. simpl. split. trivial. split. trivial. rewrite compose. apply H.
Qed.

Lemma compose_stat : forall t : term, tau (init_stat t) = t.
Proof.
  intros. simpl. rewrite compose. apply mult_subst_nil.
Qed.


(* et on arrive enfin au théorème final de correction de la compilation*)

Theorem correct_compilation : forall t : term, forall n : nat, closed t ->
  exists s : state, reducts_star t (tau s) /\ ((blocked s /\ reducts_sem_star (init_stat t) s)
    \/ reducts_sem_star_n n (init_stat t) s).
Proof.
  intros. elim (successor_n (init_stat t) n). intros. elim H0. intros. elim H1. intros.
  exists x0. split. rewrite <- (compose_stat t). apply correct_red_star. apply correct_init. trivial.
  exists x. apply H2. left. split. apply H2. exists x. apply H2.
  intros. elim H0. intros. exists x. split. rewrite <- (compose_stat t). apply correct_red_star. apply correct_init.
  trivial. exists n. elim H1. intros. apply H2. right. elim H1. intros. apply H2.
Qed.


