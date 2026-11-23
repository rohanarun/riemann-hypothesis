module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassLinearRelationUniqueOfNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
  {R : Type} [CommRing R] (et : Hol F.V →+* R) (M : Ideal R)

def perZDLin : (Λ →+ R) →ₗ[R] GlobalTheory.CatCoh.Z1 (K.OD et M) where
  toFun := K.perZD et M
  map_add' q q' := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦ map_add (algebraMap R S'.T.C) (q f.1.deg) (q' f.1.deg))
  map_smul' r q := Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦
    (map_mul (algebraMap R S'.T.C) r (q f.1.deg)).trans (Algebra.smul_def (A := S'.T.C) r _).symm)

end GlobalTheory.AnPer.Charts


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AnPer.perClD_relation_unique : ∀ {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : _root_.GlobalTheory.AnPer.Fam Empty g Λ} (K₀ : _root_.GlobalTheory.AnPer.Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : _root_.GlobalTheory.AnPer.Hol F₀.V →+* R) (M : Ideal R), K₀.Rich → (∀ z, z ∈ F₀.V) → IsNilpotent M → (∀ (f : _root_.GlobalTheory.AnPer.Hol F₀.V), ∀ z ∈ F₀.V, et f = algebraMap ℂ R (f.fn z)) → ∀ {io : Type} (S : Finset io) (d : io → R) (q : io → (Λ →+ R)) (q' : Λ →+ R), K₀.perClD et M q' = ∑ i ∈ S, d i • K₀.perClD et M (q i) → ∀ l, q' l = ∑ i ∈ S, d i * q i l := by
  intro g Λ _ F₀ K₀ R _ _ et M hrich hV hnil het io S d q q' hrel l
  let q'' : Λ →+ R := q' - ∑ i ∈ S, d i • q i
  have hq'' : ∀ m, q'' m = q' m - ∑ i ∈ S, d i * q i m := by
    intro m
    simp [q'', smul_eq_mul]
  have hcl : K₀.perClD et M q'' = 0 := by
    have hc : ∀ p : Λ →+ R, K₀.perClD et M p =
        _root_.GlobalTheory.CatCoh.H1.mk _
          (K₀.perZDLin et M p) := fun p => rfl
    simp only [hc] at hrel ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [q'', map_sub, map_sum, map_smul, hrel, sub_self]
  have hG : ∃ G : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k),
      (∀ k a, LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw (W := K₀.W k) a).toLinearMap (G k) = 0) ∧
      ∀ l k k' (h : K₀.le l k' k), G k' - Algebra.TensorProduct.map (AlgHom.id ℂ R)
        (_root_.GlobalTheory.AnPer.Charts.shA h) (G k) = q'' l ⊗ₜ[ℂ] 1 :=
    _root_.GlobalTheory.ChartCobd.coboundary_on_charts K₀ et M hnil het q'' hcl
  obtain ⟨G, hG0, hGsh⟩ := hG
  have hzero : q'' l = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let Φ : ∀ k, R ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol (K₀.W k) →ₗ[ℂ]
        _root_.GlobalTheory.AnPer.Hol (K₀.W k) :=
      fun k => (TensorProduct.lid ℂ _).toLinearMap ∘ₗ LinearMap.rTensor _ φ
    have hΦ : ∀ k r h, Φ k (r ⊗ₜ h) = φ r • h := by
      intro k r h
      simp [Φ]
    have hΦd : ∀ k a y, _root_.GlobalTheory.AnPer.dw a (Φ k y) =
        Φ k (LinearMap.lTensor R (_root_.GlobalTheory.AnPer.dw (W := K₀.W k) a).toLinearMap y) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r h =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp [hΦ]
      | add y z hy hz =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp only [map_add (f := _), hy, hz]
    have hΦs : ∀ {m k k'} (h : K₀.le m k' k) y,
        Φ k' (Algebra.TensorProduct.map (AlgHom.id ℂ R)
          (_root_.GlobalTheory.AnPer.Charts.shA h) y) =
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k y) := by
      intro m k k' h y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp [hΦ, ← _root_.GlobalTheory.AnPer.Charts.shA_apply]
      | add y z hy hz =>
        set_option synthInstance.maxHeartbeats 400000 in
          simp only [map_add (f := _), hy, hz]
    have hfsh : ∀ m k k' (h : K₀.le m k' k),
        _root_.GlobalTheory.AnPer.Charts.sh h (Φ k (G k)) =
          Φ k' (G k') + K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) := by
      intro m k k' h
      have h1 := congrArg (Φ k') (hGsh m k k' h)
      rw [map_sub, hΦs, hΦ] at h1
      have h2 : K₀.cst k' (algebraMap ℂ _ (-(φ (q'' m)))) =
          -(φ (q'' m) • 1) := by
        unfold _root_.GlobalTheory.AnPer.Charts.cst
        simp [Algebra.algebraMap_eq_smul_one]
      rw [h2, ← h1]
      abel
    obtain ⟨Gf, -, -, hper, hconst⟩ := _root_.GlobalTheory.AnPer.Charts.glue K₀
      hrich (fun k => Φ k (G k)) (by
        intro k k' h
        simp [hfsh 0 k k' h])
    have hc := hconst (fun k a => by rw [hΦd, hG0, map_zero])
    let p : _root_.GlobalTheory.AnPer.Tot Empty g := ((0 : Empty → ℂ), (0 : Fin g → ℂ))
    have hp := hper l (algebraMap ℂ _ (-(φ (q'' l)))) (fun k k' h => hfsh l k k' h) p (hV _)
    have e : Gf (F₀.shift l p) = Gf p := by
      calc Gf (F₀.shift l p) =
          Gf ((F₀.shift l p).1, (F₀.shift l p).2) := rfl
        _ = Gf ((F₀.shift l p).1, 0) := hc _ (hV _) _
        _ = Gf (p.1, 0) := by rw [Subsingleton.elim (F₀.shift l p).1 p.1]
        _ = Gf p := rfl
    have hfn : (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol F₀.V)
        (-(φ (q'' l)))).fn p.1 = -(φ (q'' l)) := by
      unfold _root_.GlobalTheory.AnPer.Hol.fn
      simp [hV]
    rw [e, hfn] at hp
    linear_combination hp
  rw [← sub_eq_zero, ← hq'' l]
  exact hzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFormalLogLiftCharacterSeries
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc _root_.WittVector

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharPeriod

theorem pow_dvd_of_theta_pow_dvd : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (x : B) (N : ℕ), (p : O) ∣ θ x ^ N → ∃ M : ℕ, (p : B) ∣ x ^ M := by
  intro p _ B O Q _ _ _ _ θ hF x N ⟨o, ho⟩
  obtain ⟨b, rfl⟩ := hF.surj o
  have hj : θ (x ^ N - p * b) = 0 := by rw [map_sub, map_pow, ho, map_mul, map_natCast, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hj
  refine ⟨N * p, ?_⟩
  have h1 : (x ^ N - (x ^ N - p * b)) ∣ (x ^ N) ^ p - (x ^ N - p * b) ^ p := sub_dvd_pow_sub_pow _ _ _
  rw [sub_sub_cancel] at h1
  rw [pow_mul]
  have h2 : (x ^ N) ^ p = ((x ^ N) ^ p - (x ^ N - p * b) ^ p) + p * y := by rw [hy]; ring
  rw [h2]
  exact dvd_add (dvd_trans (dvd_mul_right _ _) h1) (dvd_mul_right _ _)

theorem root_iterate_pow {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    (n : ℕ) (y : PreTilt O p) : (root^[n] y) ^ (p ^ n) = y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    exact (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply y

theorem one_add_pow_of_sq_zero {R : Type} [CommRing R] {x : R} (hx : x * x = 0) (k : ℕ) :
    (1 + x) ^ k = 1 + k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * hx

theorem pow_mul_logValue : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p), IsPrimitiveSystem ε → ∀ (F : BFrame ε) [Algebra ℚ F.Q] (n k : ℕ) (w : F.B) (q : F.Q), F.θ w = zeta ε n ^ k → HasVal p (fun _ : Unit => w - 1) (PowerSeries.log F.Q : MvPowerSeries Unit F.Q) q → ∃ b : F.B, (p : F.Q) ^ n * q = algebraMap F.B F.Q (k * F.a (Sandwich.mu ε) + p ^ n * b) := by
  intro p _ O _ _ _ ε hε F _ n k w q hw hq
  have hF := F.frame
  haveI := hF.complete
  set r : F.B := F.a (teichmuller p (root^[n] ε)) with hr
  have hθr : F.θ r = zeta ε n := by rw [hr, F.θ_a, fontaineTheta_teichmuller]; rfl
  have hrp : r ^ (p ^ n) = 1 + F.a (Sandwich.mu ε) := by
    rw [hr, ← map_pow, ← map_pow, root_iterate_pow, Sandwich.mu, map_sub, map_one]
    ring
  set x : F.B := (k : F.B) * F.a (Sandwich.mu ε) with hx
  have hxx : x * x = 0 := by
    have h : F.a (Sandwich.mu ε) * F.a (Sandwich.mu ε) = 0 := by
      rw [← F.p_τ]; linear_combination ((p : F.B) * p) * F.τ_sq
    linear_combination ((k : F.B) * k) * h
  set e : F.B := r ^ k with he
  have hθe : F.θ e = zeta ε n ^ k := by rw [he, map_pow, hθr]
  have hep : e ^ (p ^ n) = 1 + x := by
    have h : F.a (Sandwich.mu ε) * F.a (Sandwich.mu ε) = 0 := by
      rw [← F.p_τ]; linear_combination ((p : F.B) * p) * F.τ_sq
    rw [he, ← pow_mul, mul_comm, pow_mul, hrp, one_add_pow_of_sq_zero h]
  have hpe : (p : F.B) ∣ (e - 1) ^ (p ^ n) := by
    obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) (e - 1) 1 n
    rw [sub_add_cancel, one_pow, hep] at hs
    refine ⟨k * F.τ - (e - 1) * s, ?_⟩
    have : (p : F.B) * F.τ = F.a (Sandwich.mu ε) := F.p_τ
    linear_combination -hs + hx - (k : F.B) * this
  have hnile : ∀ i : Unit, ∃ N : ℕ, (p : F.B) ∣ (fun _ : Unit => e - 1) i ^ N := fun _ => ⟨_, hpe⟩
  have hnilw : ∀ i : Unit, ∃ N : ℕ, (p : F.B) ∣ (fun _ : Unit => w - 1) i ^ N := by
    intro _
    have h1 : F.θ (w - 1) = F.θ (e - 1) := by rw [map_sub, map_sub, hw, hθe]
    obtain ⟨s, hs⟩ := hpe
    exact pow_dvd_of_theta_pow_dvd p F.B O F.Q F.θ hF (w - 1) (p ^ n)
      ⟨F.θ s, by rw [h1, ← map_pow, hs, map_mul, map_natCast]⟩
  have hD := _root_.GlobalTheory.QLog.LogDiff.dIn_log F.B F.Q
  obtain ⟨q₁, hq₁, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p F.B O F.Q F.θ hF Unit (fun _ => e - 1) hnile _ hD
  have hJ : ∀ y ∈ RingHom.ker F.θ, ∃ y' ∈ RingHom.ker F.θ, y ^ p = p * y' := by
    intro y hy
    obtain ⟨y', hy', h⟩ := hF.pd y hy
    exact ⟨y', hy', h⟩
  obtain ⟨j, -, b', hjb⟩ := _root_.GlobalTheory.HasValCong.hasVal_sub_mem p F.B O F.Q F.θ hF Unit (fun _ => w - 1) hnilw
    (RingHom.ker F.θ) hJ (fun _ => e - 1) _ q q₁
    (fun _ => by rw [RingHom.mem_ker, sub_sub_sub_cancel_right, map_sub, hw, hθe, sub_self]) hD hq hq₁ 0
  obtain ⟨Ev, hEv, -⟩ := (_root_.GlobalTheory.CEval.continuous_eval p F.B F.B Unit (fun _ => e - 1) hnile).1
  set u : Unit → MvPowerSeries Unit F.B := fun _ => (1 + X ()) ^ (p ^ n) - 1 with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := fun _ => by simp [hu]
  have hEu : (fun j => Ev (u j)) = fun _ : Unit => x := by
    funext j
    simp only [hu, map_sub, map_pow, map_add (f := _), map_one, hEv.1 ()]
    rw [add_sub_cancel, hep, add_sub_cancel_left]
  have h1 : HasVal p (fun j => Ev (u j)) (PowerSeries.log F.Q : MvPowerSeries Unit F.Q) (algebraMap F.B F.Q x) := by
    rw [hEu]; exact _root_.GlobalTheory.QLog.SqZero.hasVal_log_of_mul_self_eq_zero F.B F.Q p x hxx
  have h2 := _root_.GlobalTheory.QLog.hasVal_subst p F.B O F.Q F.θ hF Unit (fun _ => e - 1) hnile Ev hEv Unit u _ _ hu0 hD h1
  rw [hu, _root_.GlobalTheory.Proof.subst_one_add_X_pow_log_eq_nsmul.subst_pow_log F.B F.Q (p ^ n)] at h2
  have h3 := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p F.B O F.Q F.θ hF Unit (fun _ => e - 1) _ 0 q₁ 0 hq₁).2.1 ((p ^ n : ℕ) : F.Q)
  have h4 := HasVal.unique hF h3 h2
  refine ⟨j + b', ?_⟩
  rw [pow_zero, one_mul] at hjb
  have h5 : q = q₁ + algebraMap F.B F.Q (j + b') := by rw [← hjb]; ring
  rw [h5, mul_add, ← Nat.cast_pow, h4]
  simp only [map_add (f := _), map_mul, map_natCast, map_pow]
  push_cast
  ring

theorem hasPeriod_formalLog_char : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε) (F : BFrame ε) [Algebra ℚ F.Q] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (g : MvPowerSeries (Fin d) F.B), constantCoeff g = 1 → (∀ n, c.ev n (map F.θ g) = charElem χ n) → ∀ t, c.HasPeriod F.θ t (formalLog (map (algebraMap F.B F.Q) g)) (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F _ G d c χ g hg1 hgχ t
  have hF := F.frame
  haveI := hF.complete
  have hD : DIn (⊤ : Ideal F.B) (formalLog (map (algebraMap F.B F.Q) g)) := _root_.GlobalTheory.QLog.dIn_top_formalLog_map F.B F.Q (Fin d) g hg1
  have hnil : ∀ n (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → ∀ i, ∃ N : ℕ, (p : F.B) ∣ z i ^ N := by
    intro n z hz i
    obtain ⟨N, w, hw⟩ := c.nil n i
    exact pow_dvd_of_theta_pow_dvd p F.B O F.Q F.θ hF (z i) N ⟨t.pt n w, by rw [hz, ← map_pow, hw, map_mul, map_natCast]⟩
  have hex : ∀ (n : ℕ) (z : Fin d → F.B), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → ∃ q : F.Q, HasVal p z (formalLog (map (algebraMap F.B F.Q) g)) q :=
    fun n z hz => (_root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p F.B O F.Q F.θ hF (Fin d) z (hnil n z hz) _ hD).exists
  have hcong : ∀ (n : ℕ) (z : Fin d → F.B) (q : F.Q), (∀ i, F.θ (z i) = t.pt n (c.x n i)) → HasVal p z (formalLog (map (algebraMap F.B F.Q) g)) q → ∃ b : F.B, (p : F.Q) ^ n * q = algebraMap F.B F.Q (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ)) + p ^ n * b) := by
    intro n z q hz hq
    obtain ⟨E, hE, -⟩ := (_root_.GlobalTheory.CEval.continuous_eval p F.B F.B (Fin d) z (hnil n z hz)).1
    have hq1 := _root_.GlobalTheory.QLog.hasVal_log_of_hasVal_formalLog p F.B O F.Q F.θ hF (Fin d) z (hnil n z hz) E hE g q hg1 hq
    have hθ := _root_.GlobalTheory.QLogPeriod.theta_eval_char p O ε hε F G d c χ g hgχ t n z hz (hnil n z hz) E hE
    obtain ⟨b, hb⟩ := pow_mul_logValue p O ε hε F n _ (E g) q hθ hq1
    set a := epsPairing hε G t χ
    obtain ⟨e, he⟩ := GlobalTheory.PDiv.pow_dvd_sub_digit n a
    have hy : F.a (Sandwich.mu ε * ofPadic p O a) = (GlobalTheory.PDiv.digit n a : F.B) * F.a (Sandwich.mu ε) + p ^ n * F.a (Sandwich.mu ε * ofPadic p O e) := by
      have h2 : ofPadic p O a = ofPadic p O (GlobalTheory.PDiv.digit n a : ℤ_[p]) + ofPadic p O ((p : ℤ_[p]) ^ n * e) := by
        rw [← map_add (f := _), ← he, add_sub_cancel]
      rw [h2]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    refine ⟨b - F.a (Sandwich.mu ε * ofPadic p O e), ?_⟩
    rw [hb, hy]
    congr 1
    ring
  first
  | exact ⟨hex, hcong⟩
  | exact hcong

end GlobalTheory.CharPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem push_mem_liftFil_of_injective : AbelianDeRham →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (S : Type) [CommRing S] (σ : S →+* R), Function.Injective σ →
  ∀ (J : Ideal S) (hJ : J ^ 2 = 0) (S₀ : Type) [CommRing S₀] (πS : S →+* S₀),
    Function.Surjective πS → RingHom.ker πS = J →
  ∀ (ι₀ : S₀ →+* R₀), ι₀.comp πS = π.comp σ →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i)
    (AS₀ : Over (Sp S₀)) [GrpObj AS₀] (AS : Over (Sp S)) [GrpObj AS] (iS : AS₀.left ⟶ AS.left)
    (hAS : IsGrpPullback AS₀ AS (spMap πS) iS), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom →
  ∀ (φA : A.left ⟶ AS.left) (ψA : A₀.left ⟶ AS₀.left), IsGrpPullback A AS (spMap σ) φA →
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA → i ≫ φA = ψA ≫ iS →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j)
    (BS₀ : Over (Sp S₀)) [GrpObj BS₀] (BS : Over (Sp S)) [GrpObj BS] (jS : BS₀.left ⟶ BS.left)
    (hBS : IsGrpPullback BS₀ BS (spMap πS) jS), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
    IsAbelianScheme BS → SmoothOfRelativeDimension g' BS.hom →
  ∀ (φB : B.left ⟶ BS.left) (ψB : B₀.left ⟶ BS₀.left), IsGrpPullback B BS (spMap σ) φB →
    IsGrpPullback B₀ BS₀ (spMap ι₀) ψB → j ≫ φB = ψB ≫ jS →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (fS₀ : AS₀ ⟶ BS₀) [IsMonHom fS₀], f₀.left ≫ ψB = ψA ≫ fS₀.left →
    (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∀ d ∈ liftFil (divided₂ hJ) hAS, push (divided₂ hJ) (spMap πS) fS₀ d ∈ liftFil (divided₂ hJ) hBS := by
  intro H R _ I h R₀ _ π hπ hI S _ σ hσ J hJ S₀ _ πS hπS hJk ι₀ hι g A₀ _ A _ i hA AS₀ _ AS _ iS hAS hAab hAg
    hASab hASg φA ψA hφA hψA hiA g' B₀ _ B _ j hB BS₀ _ BS _ jS hBS hBab hBg hBSab hBSg φB ψB hφB hψB hjB
    f₀ _ fS₀ _ hf hyp d hd
  obtain ⟨_, _, HBC, HR, _⟩ := H
  letI : Algebra S R := σ.toAlgebra
  have hJI : ∀ a ∈ J, σ a ∈ I := fun a ha ↦ by
    rw [← hI, RingHom.mem_ker]
    have : πS a = 0 := by rw [← RingHom.mem_ker, hJk]; exact ha
    rw [← RingHom.comp_apply, ← hι, RingHom.comp_apply, this, map_zero]
  have hdp : IsDPMorphism (divided₂ hJ) (divided₂ h) σ := isDPMorphism_sqDP hJ h σ hJI
  have hbase : spMap ι₀ ≫ spMap πS = spMap π ≫ spMap σ := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hι]
  have mA := GrpMor.of_isGrpPullback hdp hbase hψA
  have mB := GrpMor.of_isGrpPullback hdp hbase hψB
  have nA := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφA
  have nB := GlobalTheory.Published.AbelianDeRham.bcMor (R := S) (R' := R) hφB
  have hBCA := HBC S AS g hASab hASg R A φA hφA
  obtain ⟨y, hy⟩ := hBCA.1.exists (crysToDR (divided₂ hJ) hAS d)
  obtain ⟨d', rfl⟩ :=
    (GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective HR hAab hAg (isDPNilpotent_squareZero h) hπ hI hA).2 y
  have hsurj := (HR S AS g hASab hASg J (divided₂ hJ) (isDPNilpotent_squareZero hJ) S₀ πS hπS hJk AS₀ iS hAS).2
  have hm : mA.Corr d d' := fun c ↦ by
    obtain ⟨c0, rfl⟩ := hsurj c
    have k : GrpMor (dp0 S) (𝟙 (Sp S)) AS (divided₂ h) (spMap π) A₀ σ
        (spMap ι₀ ≫ spMap πS) (ψA ≫ iS) := GrpMor.of_isGrpPullback (IsDPMorphism.comp _ mA.dp (liftMor (divided₂ hJ) hAS).dp) (by simpa using hbase) (IsGrpPullback.comp hψA hAS)
    rw [GrpMor.pull_pull (liftMor (divided₂ hJ) hAS) mA k (fun _ ↦ rfl) rfl c0,
      ← GrpMor.pull_pull nA (liftMor (divided₂ h) hA) k (fun _ ↦ rfl) hiA c0]
    exact (crysToDR_apply _ hA d' _).symm.trans ((hy c0).trans (congrArg σ (crysToDR_apply _ hAS d c0)))
  have hd' : d' ∈ liftFil (divided₂ h) hA := by
    have hle : PrimitiveSubmodule A ≤ LinearMap.ker (crysToDR (divided₂ h) hA d') := by
      rw [hBCA.2, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hy c]
      rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hd
      rw [hd c hc, map_zero]
    exact (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ hle hc
  have hpush := hyp d' hd'
  have hcorr := GrpMor.Corr.push (m := mA) mB fS₀ f₀ hf.symm hm
  have hx := crysToDR_corr (divided₂ hJ) hBS hB mB nB hjB hcorr
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator]
  rw [liftFil, Submodule.mem_comap, Fil, Submodule.mem_dualAnnihilator] at hpush
  intro c hc
  apply hσ
  show σ _ = σ 0
  rw [map_zero]
  exact (hx c).symm.trans (hpush _ (nB.isMor.pullback1_mem_hodgeFiltration hc))

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem Katz.reductionMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) (V : Type) [AddCommGroup V] [Module k V] (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] V), IsRigOf μ ρ → ∃ r : Mod p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V, (∀ (f : quasiLog p h) c w, Red p (cob1 (fun i => Katz.lift p (μ i)) f.1) c → RedV p (lin f.1) w → r (Submodule.Quotient.mk f) = ρ (c, w)) ∧ Function.Surjective r ∧ ∀ m, r m = 0 ↔ ∃ n, m = p • n := by
  intro p _ k _ _ _ d μ h V _ _ ρ hρ
  have hμ' : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  have hR1 := _root_.GlobalTheory.Katz.red_rules p k (Fin d)
  have hR2 := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  have hC := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  have hD := _root_.GlobalTheory.quasiLog_reduces p k d μ h
  have hK := _root_.GlobalTheory.Katz.quasiLog_eq_p_smul_add_int p k d μ h
  have hS := _root_.GlobalTheory.Katz.exists_quasiLog_red p k d μ h
  have hVu : ∀ (v : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v w' → w = w' := by
    intro v w w' h1 h2
    funext i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    rw [ha] at hb
    rw [← ha', ← hb', IsFractionRing.injective (WittVector p k) (Fr p k) hb]
  have hVa : ∀ (v v' : Fin d → Fr p k) (w w' : Fin d → k), RedV p v w → RedV p v' w' →
      RedV p (v + v') (w + w') := by
    intro v v' w w' h1 h2 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    obtain ⟨b, hb, hb'⟩ := h2 i
    exact ⟨a + b, by rw [Pi.add_apply, ha, hb, map_add (f := _)], by rw [map_add (f := _), ha', hb']; rfl⟩
  have hVs : ∀ (r : WittVector p k) (v : Fin d → Fr p k) (w : Fin d → k), RedV p v w →
      RedV p (fun i => algebraMap _ (Fr p k) r * v i) (WittVector.constantCoeff r • w) := by
    intro r v w h1 i
    obtain ⟨a, ha, ha'⟩ := h1 i
    exact ⟨r * a, by beta_reduce; rw [ha, ← map_mul], by rw [map_mul, ha']; rfl⟩
  have hlinadd : ∀ f g : MvPowerSeries (Fin d) (Fr p k), lin (f + g) = lin f + lin g := by
    intro f g; funext i; simp [lin]
  have hlinsmul : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      lin (r • f) = fun i => algebraMap _ (Fr p k) r * lin f i := by
    intro r f; funext i
    simp only [lin, ← algebraMap_smul (Fr p k) r f, coeff_smul, smul_eq_mul]
  have hcobs : ∀ (r : WittVector p k) (f : MvPowerSeries (Fin d) (Fr p k)),
      cob1 (fun i => Katz.lift p (μ i)) (r • f) = r • cob1 (fun i => Katz.lift p (μ i)) f := by
    intro r f
    rw [← algebraMap_smul (Fr p k) r f, formalCoboundary_smul hμ', algebraMap_smul]
  choose c w hc hw using hD.1
  have key : ∀ f (hf : f ∈ quasiLog p h) c' w', Red p (cob1 (fun i => Katz.lift p (μ i)) f) c' →
      RedV p (lin f) w' → ρ (c f hf, w f hf) = ρ (c', w') := by
    intro f hf c' w' h1 h2
    rw [hR2.2.1 _ _ _ (hc f hf) h1, hVu _ _ _ (hw f hf) h2]
  let Φ : quasiLog p h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] V :=
    { toFun := fun f => ρ (c f.1 f.2, w f.1 f.2)
      map_add' := fun f g => by
        rw [key (f + g).1 (f + g).2 (c f.1 f.2 + c g.1 g.2) (w f.1 f.2 + w g.1 g.2), ← map_add (f := _),
          Prod.mk_add_mk]
        · rw [Submodule.coe_add, formalCoboundary_add hμ']
          exact (hR2.2.2.2.1 _ _ _ _ (hc _ _) (hc _ _)).1
        · rw [Submodule.coe_add, hlinadd]
          exact hVa _ _ _ _ (hw _ _) (hw _ _)
      map_smul' := fun r f => by
        rw [key (r • f).1 (r • f).2 (WittVector.constantCoeff r • c f.1 f.2)
          (WittVector.constantCoeff r • w f.1 f.2), ← map_smul, Prod.smul_mk]
        · rw [Submodule.coe_smul, hcobs]
          exact hR2.2.2.2.2.1 _ _ _ (hc _ _)
        · rw [Submodule.coe_smul, hlinsmul]
          exact hVs _ _ _ (hw _ _) }
  have hΦ : ∀ f : quasiLog p h, Φ f = ρ (c f.1 f.2, w f.1 f.2) := fun _ => rfl
  have hker : (intBy p k (Fin d) 1).submoduleOf (quasiLog p h) ≤ LinearMap.ker Φ := by
    intro f hf
    rw [LinearMap.mem_ker, hΦ]
    have hf' : (f : MvPowerSeries (Fin d) (Fr p k)) ∈ intBy p k (Fin d) 1 := hf
    obtain ⟨b, hb⟩ := (hR1.1 _).1 hf'
    obtain ⟨h1, h2⟩ := hC.2.1 _ _ hb
    rw [key _ _ _ _ h1 h2]
    exact ((hρ.ker _ _ (hD.2 _ f.2 _ h1)).2 ⟨b, rfl, rfl⟩)
  refine ⟨Submodule.liftQ _ Φ hker, ?_, ?_, ?_⟩
  · intro f c' w' h1 h2
    rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]
  · intro v
    obtain ⟨c', w', hcoc, rfl⟩ := hρ.surj v
    obtain ⟨f, hf, h1, h2⟩ := hS c' hcoc w'
    exact ⟨Submodule.Quotient.mk ⟨f, hf⟩, by rw [Submodule.liftQ_apply, hΦ, key _ _ _ _ h1 h2]⟩
  · intro m
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [Submodule.liftQ_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨b, hb1, hb2⟩ := (hρ.ker _ _ (hD.2 _ f.2 _ (hc f.1 f.2))).1 h0
      have h1 := hc f.1 f.2
      have h2 := hw f.1 f.2
      rw [hb1] at h1
      rw [hb2] at h2
      obtain ⟨g, hg, hfg⟩ := hK f.1 f.2 b h1 h2
      refine ⟨Submodule.Quotient.mk ⟨g, hg⟩, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k), ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq]
      exact hfg
    · rintro ⟨n, hn⟩
      have : Φ f = Submodule.liftQ _ Φ hker (p • n) := by
        rw [← hn, Submodule.liftQ_apply]
      rw [← hΦ, this, map_nsmul, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]

end GlobalTheory
end

