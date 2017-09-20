(*Add Rec LoadPath "fcf/src/FCF".*)
Require Import QArith_base.
Require Import ballotPollAudit.

Require Import FCF.
Require Import Crypto.
Require Import Basics.
Require Import Bernoulli.

(*
  Implements a risk-limiting audit as described in 
 "Ballot-polling Risk-limiting Audits to Verify Outcomes" 
  https://www.usenix.org/system/files/conference/evtwote12/evtwote12-final27.pdf
*)

Definition is_some {A : Type} (o : option A) :=
match o with
| Some _ => true 
| None => false
end.

Definition nat_to_posnat_ (n : nat) : option posnat.
destruct n eqn:?. exact (None).
assert (nz n). constructor. symmetry in Heqn0.
subst.
exact (gt_Sn_O n0). 
exact (Some (pos n)).
Defined.

Definition nat_to_posnat (n : nat) : posnat.
destruct n eqn:?. exact (pos 1).
assert (nz n). constructor. symmetry in Heqn0.
subst.
exact (gt_Sn_O n0). 
exact (pos n).
Defined.

Definition get_random_ballot' (votes : list (option bool)) : Comp (option bool) :=
(n <-$ (RndNat (nat_to_posnat (length votes))) ; ret (nth n votes (None))).

Definition get_random_ballot_ratio (ratio : Rat) : Comp bool :=
Bernoulli ratio.

Definition get_random_ballot votes :=
match votes with
| nil => ret None
| _ => get_random_ballot' votes
end.

(* A None vote is considered invalid *)
Definition is_winner_vote (o : option bool) :=
match o with
| Some true => true
| _ => false
end.

Definition is_loser_vote (o : option bool) :=
match o with
| Some false => true
| _ => false
end.

Definition count {A} (f : A -> bool) (l : list A) :=
length (filter f l).

Lemma get_random_ballot_wf : forall v, 
    well_formed_comp (get_random_ballot v).
intros. 
unfold get_random_ballot. 
destruct v; wftac.
unfold get_random_ballot'.
simpl. wftac.
Qed.

Hint Resolve get_random_ballot_wf : wftac.


Instance EqDecOptionBool : EqDec (option bool).
apply _.
Qed.

Definition nat_to_rat n := RatIntro n (pos 1). 

Definition tabulate (votes : list (option bool)) :=
(count is_winner_vote votes, count is_loser_vote votes).

Lemma tabulate_sumlist : forall votes winners losers,
length votes <> O ->
tabulate votes = (winners, losers) ->
sumList (allNatsLt (nat_to_posnat (length votes)))
     (fun z : nat => evalDist (ret nth z votes None) (Some true)) == (nat_to_rat winners).
intros. destruct votes. intuition.
clear H.
generalize dependent winners.
revert o losers.
induction votes; intros.
- simpl in *. unfold sumList. simpl. 
  dist_compute.
  + subst. unfold tabulate in H0. unfold count in H0 at 1.
    simpl in H0. inversion H0.
    unfold nat_to_rat.
    reflexivity.  
  + unfold tabulate, count in H0.
    destruct o eqn:?. 
     * destruct b;  intuition. 
       simpl in *. inversion H0; auto.
       unfold nat_to_rat. reflexivity. 
     * subst. 
       simpl in *. inversion H0; auto.
       unfold nat_to_rat.
       reflexivity.

- simpl in *. rewrite sumList_app.  
  destruct a eqn:?.
  + 
Admitted.
  




Lemma random_prob' : forall votes winnervotes loservotes totalvotes,
tabulate votes = (winnervotes,loservotes ) ->
nat_to_posnat_ (length votes) = Some totalvotes ->
evalDist (get_random_ballot votes) (Some true) ==
RatIntro (winnervotes) (totalvotes). 
intros.
destruct votes. inversion H0.
unfold get_random_ballot, get_random_ballot'.
rewrite RndNat_seq. remember (cons o votes) as all_votes. 
rewrite (sumList_filter_partition (compose is_winner_vote (fun n => nth n votes None))).
(*
rewrite (sumList_filter_partition (compose is_loser_vote (fun n => nth n votes None))) at 2.

specialize (H1 (allNatsLt (length votes))).
rewrite (sumList_filter_partition (is_winner_vote)).
SearchAbout sumList. Print sumList.
eapply eqRat_trans. Check RndNat_seq.
change (ret nth n (o :: votes) None) with (fun n => ret nth n (o :: votes) None).
apply RndNat_seq.
SearchAbout evalDist.
*)
Admitted.

Lemma random_prob :  forall votes winnervotes loservotes totalvotes,
tabulate votes = (winnervotes,loservotes ) ->
nat_to_posnat_ (length votes) = Some totalvotes ->
Pr[v <-$ (get_random_ballot votes); ret (is_winner_vote v)] ==
RatIntro (winnervotes) (totalvotes). 
intros. destruct votes eqn:?. inversion H0.
unfold get_random_ballot, get_random_ballot'.
pose proof  RndNat_prob. 
specialize (H1 (length (o :: votes))). 
eapply eqRat_trans.
(*SearchAbout RndNat. SearchAbout evalDist. Print Distribution.*)




(*Print getSupport. Print getAllBvectors.*)
(*Compute (getAllBvectors 2).*)
(*Print Bind.*)
simpl.
(*Check evalDist_seq_case_split_eq. 
SearchAbout evalDist.*)
Admitted.



Fixpoint sampleBallots' (toSample : nat)  (votes : list (option bool)) : Comp (list (option bool)) :=
match toSample with
| O => ret (nil)
| S x' => n <-$ (RndNat (length votes)); 
          r <-$ (sampleBallots' x'  votes);
          ret (cons (nth n votes (None)) r)
end.

Definition sampleBallots toSample votes :=
match votes with
| nil => ret nil
| _ => sampleBallots' toSample votes
end.

Lemma sampleBallots_wf : forall c v, 
    well_formed_comp (sampleBallots c v).
intros. 
unfold sampleBallots. 
destruct v; wftac. 
induction c; simpl; wftac. 
Qed.




Local Open Scope nat.

Lemma plus_gt_0 :
forall (a b : nat),
a > 0 ->
a + b > 0.
intros.
induction a; omega.
Qed.

Definition posnatAdd (p1 : posnat) (n : nat) : posnat. 
destruct p1.
exact (@natToPosnat (x + n) (Build_nz (plus_gt_0 x n g))). 
Defined.

Definition winner_margin v : option Rat:=
let (winvotes, losevotes) := tabulate v in
option_map (fun v => RatIntro winvotes (posnatAdd v losevotes)) (nat_to_posnat_ winvotes).

Definition posnat_to_pos (p : posnat) : positive.
destruct p.
exact (Pos.of_nat x).
Defined.


Definition Rat_to_Q r :=
match r with 
| RatIntro n d => Z.of_nat n # posnat_to_pos d
end.

Definition gtb a b := 
match nat_compare a b with
| Gt => true 
| _ => false
end.

(* An audit where you count every vote *)
Definition full_count_audit (votes : list (option bool)) (_ : Q) (_ : Q) :=
let (rep_winner_count, rep_loser_count) := tabulate votes in
if (gtb rep_winner_count rep_loser_count) then
    ret true
else
    ret false.

(*  T = (2*s_w)^{m_w} * (2 - 2*s_w)^{m_l}  *)
Definition update_T (vote : bool) (T : Q) (winnerShare : Q) :=
if vote then
  (((2 # 1) * winnerShare) * T)%Q
else
  (((2 # 1) * (1 - winnerShare)) * T)%Q
.

(* UPDATE: back-of-the-napkin calculations have given evidence
that the note below might not actually be valuable.

 Note: it has been proposed that this bound can be reduced
 to the Chebyshev's inequality. Proving this first in FCF
 may be a good step forward. 

Chebyshev inequality: Pr[ |X-u| >= ks] <= 1/(k^2) 
*)

(* Wald's SPRT risk-limiting audit procedure *)
Fixpoint do_audit_inc' total_votes votes T margin risk : Comp bool :=
match total_votes with 
| O => full_count_audit votes risk margin
| S n => b <-$ get_random_ballot votes;
        (match b with
         | Some vote => 
           let T' := update_T vote T margin in
           if (Qlt_bool T' risk) then
             ret true
           else
             do_audit_inc' n votes T' margin risk
         | None => do_audit_inc' n votes T margin risk
         end)
end.

(* An audit returns true if the election result is likely correct, and false otherwise *)
Fixpoint do_audit_inc_rat' T n total_votes actual_margin reported_margin risk : Comp bool :=
match total_votes with 
| O => ret false
| S total_votes' => vote <-$ get_random_ballot_ratio actual_margin;
        let T' := update_T vote T reported_margin in
        if (Qlt_bool T' risk) then
          ret true
        else
          do_audit_inc_rat' T' (S n) total_votes' actual_margin reported_margin risk
end.

(* Initialize the audit with test statistic T=1 and ballots sampled m=0 *)
Definition do_audit_inc_rat total_votes actual_margin reported_margin risk : Comp bool :=
do_audit_inc_rat' 1 0 total_votes actual_margin reported_margin risk .

Definition isProb_Q (a : Q) :=
(a <= 1)%Q.

Definition isUncertain_Q (a : Q) :=
~ (a == 0)%Q /\ ~(a == 1)%Q.

Definition isProb_Rat (a : Rat) :=
(a <= 1)%rat.

Definition isUncertain_Rat (a : Rat) :=
~ (a == 0)%rat /\ ~(a == 1)%rat.

Definition lose_game_prob_only (audit : nat -> Rat -> Q -> Q -> Comp bool)
           total_votes (actual_margin : Rat) (reported_margin : Q) risk:=
  if (Qle_bool (Rat_to_Q actual_margin) (1 # 2))
  then audit total_votes actual_margin reported_margin risk
  else ret false.

Definition valid_audit_prob_only audit :=
forall total_votes actual_margin reported_margin risk,
  isProb_Rat actual_margin ->
  isProb_Q reported_margin ->
  isUncertain_Rat (actual_margin) ->  
  leRat (Pr [lose_game_prob_only audit total_votes actual_margin reported_margin (Rat_to_Q risk)])
        risk.


Ltac if_match_tac :=
match goal with
|  [  |- context [ if ?b then _ else _ ] ] => 
   destruct b eqn:?
|  [ |- context [ match ?m with _ => _ end ] ] =>
   destruct m eqn:?
end.

(* What is this saying? Is it true? *)
Lemma get_support_bernoulli_nz :
forall n f,
~(n == 0)%rat ->
~(n == 1)%rat ->
(n <= 1)%rat ->
sumList (getSupport (Bernoulli n)) f == sumList (cons true (cons false nil)) f.
intros.
pose proof (getSupport_correct (Bernoulli n)).
unfold Support in *.
destruct H2.
assert (In true (getSupport (Bernoulli n))).
apply H3. intro. rewrite Bernoulli_correct in H4. intuition.
auto.
assert (In false (getSupport (Bernoulli n))).
apply H3. intro.
rewrite Bernoulli_correct_complement in H5.
apply ratSubtract_0_inv in H5. 
apply leRat_impl_eqRat in H5; auto. auto.
destruct (getSupport (Bernoulli n)) eqn:?. inversion H4.
destruct l. destruct b; simpl in *; intuition; try congruence. 
simpl in *. destruct l. destruct b, b0; intuition; try congruence; auto.
unfold sumList. simpl. repeat rewrite <- ratAdd_0_l.
(*rewrite (ratAdd_comm (f false) (f true)). reflexivity.
inversion H2. subst. destruct b, b0, b1; try intuition.
inversion H9. intuition.
inversion H9; intuition.
inversion H9; intuition.
inversion H9; intuition.
Qed.*)
Admitted.


Lemma plus_minus_1 : forall (m : Rat), 
(m <= 1)%rat ->
(m + (ratSubtract 1 m)%rat)%rat == 1%rat.
intros.
rewrite <- ratSubtract_ratAdd_assoc; auto.
rewrite ratSubtract_ratAdd_inverse. reflexivity.
Qed.

Definition bool_to_nat (b: bool) :=
if b then 1 else 0.

Fixpoint n_bernoulli (n : nat) R : Comp nat :=
match n with
| O => (b <-$ (Bernoulli R);
        ret (bool_to_nat b))
| S n => b <-$ Bernoulli R;
         r <-$ n_bernoulli n R;
         ret ((bool_to_nat b) + r)
end.

Definition do_binomial x (N : posnat) R :=
b <-$ n_bernoulli N R;
ret leb x b.

Lemma nat_lt_gt : forall x y,
x < y <-> y > x.
intros. omega.
Qed.

Definition fact_posnat (x : posnat) : posnat.
assert (nz (fact x)) by (constructor; rewrite <- nat_lt_gt; apply lt_O_fact).
apply (pos (fact x)).
Defined.

Definition fact_nat_posnat (x : nat) : posnat.
assert (nz (fact x)) by (constructor; rewrite <- nat_lt_gt; apply lt_O_fact).
apply (pos (fact x)).
Defined.

Fixpoint ratPower (r : Rat) (n : nat) : Rat :=
match n with
| O => 1%rat
| S n' => (r * ratPower r n')%rat
end.

Definition choose (N : posnat) (x : nat) : Rat :=
RatIntro (fact N) (posnatMult (fact_nat_posnat x) (fact_nat_posnat (N - x))).

Definition binomial (N : posnat) (x : nat) (r : Rat) : Rat :=
((choose N x) * (ratPower r x) * (ratPower (ratSubtract 1%rat r)%rat (N - x)))%rat.

Lemma n_bernoulli_binomial :
forall N x R,
Pr[ do_binomial x N R ] == binomial N x R.  
Proof.


intros.
destruct N.
destruct x0. omega.

generalize dependent g.

induction x0. intros. 
unfold binomial. unfold choose. simpl fact.
simpl ratPower.
unfold do_binomial. unfold evalDist. fold evalDist.
simpl n_bernoulli. unfold getSupport.
Admitted.

Lemma do_audit_inc_rat'_correct : 
forall R T n, 
R T n ->
valid_audit_prob_only (do_audit_inc_rat' T n).
Proof.
  intros. unfold valid_audit_prob_only.
  intros.
  induction total_votes.
  - unfold lose_game_prob_only.
    if_match_tac; dist_compute; apply rat0_le_all. 
  - unfold lose_game_prob_only. simpl. if_match_tac.
    simpl. rewrite get_support_bernoulli_nz. 
    unfold sumList.
    simpl. dist_compute_simp.
    rewrite Bernoulli_correct.
    rewrite Bernoulli_correct_complement.
     { repeat if_match_tac. 
        - simpl. dist_compute. rewrite plus_minus_1.
Admitted.      
    



Lemma do_audit_inc'_wf :
forall total_votes votes T margin risk,
well_formed_comp (do_audit_inc' total_votes votes T margin risk).
induction total_votes; intros; simpl; wftac.
simpl. unfold full_count_audit; wftac.
simpl. intros. destruct b; simpl; wftac.
Qed.



Fixpoint do_audit' total_votes votes winnerseen loserseen margin risk : Comp bool :=
match total_votes with
| O => ret (false)
| S n => b <-$ get_random_ballot votes;
        (match b with 
        | Some true => match (auditDone (N.of_nat (S winnerseen)) (N.of_nat loserseen) margin risk) with
                       | true => ret (true)
                       | false => (do_audit' n votes (S winnerseen) loserseen margin risk)
                       end
        | Some false => do_audit' n votes winnerseen (S loserseen) margin risk
        | _ => do_audit' n votes winnerseen loserseen margin risk
        end)
end.


Lemma do_audit'_wf :
forall tv v ws ls m r, well_formed_comp (do_audit' tv v ws ls m r).
induction tv; intros; unfold do_audit'.
wftac. simpl. wftac. 
intros.
repeat if_match_tac; wftac.
Qed.


Definition do_audit votes risk margin :=
do_audit' (length votes) votes 0 0 (Rat_to_Q margin) risk.

Definition do_audit_inc votes risk margin :=
do_audit_inc' (length votes) votes 0 margin risk.

Definition vote_to_win_lose (winner loser vote : nat) : option bool :=
if (beq_nat winner vote) then
  Some true
else
  if (beq_nat loser vote) then
    Some false
  else
    None.

Definition votes_to_win_lose (winner loser : nat) votes :=
map (vote_to_win_lose winner loser) votes.


Lemma gtb_gt_iff : forall a b, gtb a b = true <-> a > b.
Proof.
intros.
split; intros;
destruct (nat_compare a b) eqn:?; intuition; 
try rewrite <- nat_compare_gt in *; 
try rewrite <- nat_compare_lt in *;
try rewrite nat_compare_eq_iff in *; try omega; auto.
 - unfold gtb in H. 
   destruct (a?=b) eqn:?; try congruence. 
   rewrite <- nat_compare_gt in Heqc0. 
   omega.   
 - unfold gtb in H. destruct (a?=b) eqn:?; try congruence. 
   rewrite <- nat_compare_gt in Heqc0.
   assumption. 
 - unfold gtb. 
   destruct (a?=b) eqn:?. 
   + rewrite nat_compare_eq_iff in Heqc0. 
     omega. 
   + rewrite <- nat_compare_lt in Heqc0. 
     omega. 
   + reflexivity. 
Qed. 

(* The audit wins: 
 - trivially if there are no votes
 - if the reported winner is the actual winner
 - if the audit catches a misreported margin
*)
Definition win_game (audit : list (option bool) -> Q -> Q -> Comp bool)
           (actual_votes : list nat) (reported_winner : nat)
           (reported_loser : nat) (reported_margin : Q) risk  :=
  if (beq_nat (length actual_votes)  0)
  then ret true
  else
    let win_loss_votes := votes_to_win_lose reported_winner reported_loser actual_votes in
    let (rep_winner_count, rep_loser_count) := tabulate win_loss_votes in
    if (gtb rep_winner_count rep_loser_count) then
      ret true
    else
      result <-$ audit win_loss_votes risk reported_margin;
      ret (negb result)
.


(* An audit is valid if Pr[audit_loses] < risk *)
Definition valid_audit audit := 
forall actual_votes reported_winner
       reported_loser reported_margin risk,
  leRat (ratSubtract 1%rat risk) 
         (Pr[win_game audit actual_votes reported_winner 
                      reported_loser (Rat_to_Q risk)
                      reported_margin]).

(* A full-count audit is always valid *)
Lemma valid_full_count : 
  valid_audit full_count_audit.
Proof.
  intros.
  unfold valid_audit.
  intros.
  unfold win_game. if_match_tac.
  - dist_compute. apply ratSubtract_le. auto.
  - simpl in *. if_match_tac. dist_compute. apply ratSubtract_le; auto.
    unfold full_count_audit. simpl in *. rewrite Heqb0. simpl.
    dist_compute. apply ratSubtract_le; auto.
Qed.

Lemma evalDist_negb : forall (c : Comp bool) (a : bool),
    evalDist (x <-$ c; ret (negb x)) a == evalDist (x <-$ c; ret x) (negb a).
Proof. 
  intros.

  simpl. rewrite sumList_body_eq. 
  instantiate (1:=(fun b:bool => evalDist c b *
                    (if EqDec_dec bool_EqDec b (negb a) then 1 else 0))%rat).
  reflexivity.
  intros.
  simpl.

  destruct a0, a eqn:?.
  dist_compute.
  dist_compute.
  dist_compute.
  dist_compute.
Qed.

Lemma not_true_length : forall l,
~In true l -> length (filter (fun b => b) l) = 0.
intros.
induction l. auto.
simpl in *. destruct a. simpl in *. intuition.
intuition.
Qed.

Lemma length_filter_true_bool :
forall l,
NoDup l ->
length (filter (fun b : bool => b) l) <= 1.
intros.
induction l. simpl. auto.
simpl. destruct a. simpl. inversion H.
intuition.
subst. 
rewrite not_true_length. auto. auto.
inversion H. auto.
Qed.

Lemma ratone_rat :
(1/1 == 1)%rat.
rattac. inversion H0.
auto.
Qed.

Lemma rat_ratone :
(1 == 1/1)%rat.
rattac. inversion H0.
auto.
Qed.

Lemma lognat_0_unique :
forall x, lognat x = 0 -> x = 0.
intros.
induction x. auto.
unfold lognat in H. simpl in *. 
destruct (Pos.of_succ_nat x) eqn:?.
simpl in *. congruence. simpl in H. intuition. simpl in *. congruence.
Qed.



(*Lemma sumlist_support_superSet :*)


Lemma of_nat_posnat : 
forall (p: posnat), Z.of_nat p = Zpos (posnat_to_pos p).
Proof.
intros.
destruct p. simpl. unfold Z.of_nat. destruct x; try omega.
f_equal. apply Pos.of_nat_succ.
Qed.

Lemma le_Q_Rat :
forall r s, 
Qle_bool (Rat_to_Q r) (Rat_to_Q s) =true -> leRat r s.
Proof.
intros.
destruct r. destruct s. simpl in *.
unfold Qle_bool in H. simpl in *. unfold leRat, bleRat. simpl.
if_match_tac; auto. exfalso. 
clear Heqs.
apply inj_gt in g.
repeat rewrite Nat2Z.inj_mul in g.
repeat rewrite of_nat_posnat in g. rewrite <-Zle_is_le_bool in H.
omega.
Qed.

Lemma valid_ballot_poll_inc_rat :
  valid_audit_prob_only do_audit_inc_rat.
Proof.
  unfold valid_audit_prob_only.
  intros.
  unfold lose_game_prob_only.
  if_match_tac. 
  unfold do_audit_inc_rat. remember 1%Q. clear Heqq.
  - induction total_votes.
    + simpl. unfold sumList. simpl. repeat if_match_tac; dist_compute; auto. rattac.
    + unfold do_audit_inc_rat. unfold do_audit_inc_rat'. fold do_audit_inc_rat'.
      simpl.
      unfold get_random_ballot_ratio. 
      rewrite get_support_bernoulli_nz. unfold sumList. simpl. 
      rewrite Bernoulli_correct.
      rewrite Bernoulli_correct_complement. dist_compute_simp.
      remember (Qlt_bool ((2 # 1) * reported_margin * q) (Rat_to_Q risk)).
      destruct b.
      simpl.
      dist_compute_1; try congruence. dist_compute_simp.
      if_match_tac. dist_compute.
      rewrite plus_minus_1; auto.
      admit. (*believable*)
      
Local Open Scope rat.



      
      simpl. dist_compute.
      (*SearchAbout Rat.
      rewrite multRat_1_r.
      
 dist_compute.
      
      rewrite (sumList_filter_partition (fun b => b)).
      eapply leRat_trans.
      eapply ratAdd_leRat_compat.
Check sumList_all.
      rewrite sumList_all.
      Focus 2. intros. 
      apply filter_In in H. destruct H. subst.
      reflexivity.
      simpl. SearchAbout Support.
      destruct (Qlt_bool ((2 # 1) * reported_margin * 1) (Rat_to_Q risk)) eqn:?.
      simpl. rewrite Bernoulli_correct.
      eapply ratMult_leRat_compat. instantiate (1:=1%rat). 
      destruct (length
                  (filter (fun b : bool => b) (getSupport (Bernoulli actual_margin)))) eqn:?. 
      rattac.
      destruct n. rewrite ratone_rat. rattac.
      
      assert (X := length_filter_true_bool (getSupport (Bernoulli actual_margin))).
      assert ( NoDup (getSupport (Bernoulli actual_margin))) by (apply getSupport_NoDup). 
      intuition.
      
      instantiate (1:=actual_margin). 
      dist_compute. 

*)



assert ( (1 # 2) = (Rat_to_Q (RatIntro 1 (pos 2)))) by auto. 
(*rewrite H in Heqb.
apply le_Q_Rat in Heqb. 
eapply leRat_trans. apply Heqb. simpl. 
rattac. inversion H2. subst. omega. 

rewrite rat_ratone.
rattac.
simpl.
SearchAbout Z.of_nat. 
SearchAbout posnat_to_pos.
Set Printing All.
 SearchAbout Z.of_nat.

Check ratle.
Lemma Qle_





simpl
simpl. auto.
inversion H3.
subst. simpl. destruct a. simpl. 
 
      destruct a. simpl.

      SearchAbout (Rat -> Prop).*)
Admitted.

Lemma getSupport_bernoulli : forall r, 
~ r == 1%rat ->
~ r == 0%rat ->
(getSupport (Bernoulli r)) = cons true (cons false nil).
Proof.
intros. destruct r.
destruct p.
induction (lognat x) eqn:?. simpl. rewrite Heqn0. simpl.
unfold bvToNat. simpl. clear - Heqn0 g. exfalso.
induction x. omega.
unfold lognat in *. simpl in *.
unfold lognat in *.  
(*Check Pos.size_nat. Print Pos.size_nat.*)
- simpl. unfold getAllBvectors.
(*SearchAbout getSupport.
      Print Support. 
      Print evalDist.

Print bind_eq_dec.
Print Bind.*)
      simpl.
(*      Check sumList_all.*)
      (*rewrite sumList_exactly_one.
      
   
      SearchAbout evalDist.
simpl. unfold get_random_ballot_ratio at 1. unfold Bernoulli. destruct actual_margin.
Set Printing All.
Print Proper.
      rewrite (evalDist_negb (do_audit_inc_rat' (S total_votes) actual_margin reported_margin 1
       (Rat_toQ risk)) true) at 1. 
Check evalDist_right_ident.
*)
Admitted.

Theorem evalDist_right_ident : forall (A : Set)(eqd : EqDec A)(c : Comp A) a,
  evalDist (x <-$ c; ret x) a == evalDist c a.

  intuition.
  destruct (in_dec (EqDec_dec eqd) a (getSupport c)).
  simpl.
  eapply eqRat_trans.
  eapply sumList_exactly_one.
  eapply getSupport_NoDup.
  eauto.
  intuition.
  destruct (EqDec_dec eqd b a).
  subst.
  intuition.
  eapply ratMult_0_r.

  destruct (EqDec_dec eqd a a).
  eapply ratMult_1_r.
  congruence.

  simpl.
  eapply eqRat_trans.
  eapply sumList_0.
  intuition.
  destruct (EqDec_dec eqd a0 a).
  subst.
  intuition.
  eapply ratMult_0_r.
  symmetry.
  eapply getSupport_not_In_evalDist.
  trivial.
Qed.

(* Main result *)
(* Our implementation of Wald's SPRT audit is valid *)
Lemma valid_ballot_poll_inc :
  valid_audit do_audit_inc.
Proof.
  unfold valid_audit.
  intros.
  unfold win_game.
  if_match_tac.
  - dist_compute. apply ratSubtract_le. auto.
  - simpl.
    if_match_tac.
    + simpl. dist_compute. apply ratSubtract_le. auto.
    + induction actual_votes.
      * simpl. inversion Heqb. 
      * unfold votes_to_win_lose. 
        simpl map.
        unfold vote_to_win_lose at 1.
        if_match_tac.
        symmetry in Heqb1.
        apply beq_nat_eq in Heqb1.
        subst. 
(*        Check do_audit_inc.*)
Admitted.  
    