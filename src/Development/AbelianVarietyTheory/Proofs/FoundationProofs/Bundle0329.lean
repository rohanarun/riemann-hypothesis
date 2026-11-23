module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
section
noncomputable section

namespace GlobalTheory.FlatLine

theorem isAlgebraic_of_norm_const {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ = ‖P₀ b‖) : IsAlgebraic K b := by
  by_contra hb
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (2 : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = 2 * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_ofNat] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_two] at h2
  have h3 : P₀ b = 0 := norm_eq_zero.1 (by linarith)
  exact hb ((map_eq_zero P₀).1 h3 ▸ isAlgebraic_zero)

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem liesOn_frMap {Z : Comp Xo c} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) (hy : LiesOn Z y) : LiesOn Z z := by
  have e : ptF z = spMap φ.toRingHom ≫ ptF y := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
      congr 1
      ext a
      exact (φ.commutes a).symm
  intro s
  rw [e, Scheme.Hom.comp_apply]
  exact hy _

theorem liesOn_frBor {Z : Comp Xo c} {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) (hz : LiesOn Z z) : LiesOn Z y := by
  have e : ptF y = ptF z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
    · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]
  intro s
  rw [e]
  exact hz s

theorem secZ_zero_eq : secZ Xo c 0 = sec Xo c 0 0 := by
  rw [← secZ_nat]
  congr 1
  funext i
  cases i <;> rfl

theorem exists_eq_smul_idem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {b : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ = b) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ = b := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_const (K := c.F) (b := evC h Z g) P₀
    fun P => (key P).trans (key P₀).symm)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem ConstSec.exists_eq_smul (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c}
    {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) :
    ∃ (a : c.F) (ha : a ≠ 0), t = s.smul a ha := by
  have hσ := goodEmb_goodOf c c.F.val.toRingHom
  let u : ConstSec U x Z 0 0 := (t.mul s.symm).copy (add_neg_cancel la) (add_neg_cancel δ)
  obtain ⟨a, ha⟩ := exists_eq_smul_idem (U _) hσ (hU _ hσ) hF (g := u.sig) (exOf_zero (Dw := Dw) ▸ u.sig_mem)
    u.sig_mem_suppOn (b := u.cInf c.F.val.toRingHom) fun z hz => by
      rw [← homN_zero _ x, ← wtOf_zero (Dw := Dw)]; exact u.homN_eq hz
  have ha' : t.sig * s.inv = a • idem Z := ha
  have h : t.sig = a • s.sig :=
    calc t.sig = t.sig * s.inv * s.sig := by
          rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_comm, t.idem_sig]
      _ = a • s.sig := by rw [ha', smul_mul_assoc, s.idem_sig]
  have h0 : a ≠ 0 := by
    intro h0
    apply t.sig_ne_zero
    rw [h, h0]
    set_option synthInstance.maxHeartbeats 200000 in
      exact zero_smul c.F s.sig
  exact ⟨a, h0, ConstSec.ext h⟩

theorem ConstSec.deg_eq (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c}
    {la : Weight Dw} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ} (s t : ConstSec U x Z la δ) : t.deg = s.deg := by
  obtain ⟨a, ha, rfl⟩ := ConstSec.exists_eq_smul hU hF s t
  exact ConstSec.deg_smul a ha s

end GlobalTheory.FlatLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.NormSum.Term

def Bd {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (B : ℝ) (x : ℂ) : Prop :=
  x ∈ Qbar ∧ ‖lamC lam x‖ ≤ B

section
variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem lamC_coe (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC, x.2]

theorem Bd.coe {B : ℝ} {x : Qbar} (h : ‖lam x‖ ≤ B) : Bd lam B (x : ℂ) :=
  ⟨x.2, by rwa [lamC_coe]⟩

theorem Bd.mono {B B' : ℝ} {x : ℂ} (h : Bd lam B x) (hB : B ≤ B') : Bd lam B' x :=
  ⟨h.1, h.2.trans hB⟩

theorem Bd.zero {B : ℝ} (hB : 0 ≤ B) : Bd lam B 0 := by
  have := Bd.coe (lam := lam) (B := B) (x := 0) (by simpa using hB)
  simpa using this

theorem Bd.add {B : ℝ} {x y : ℂ} (hx : Bd lam B x) (hy : Bd lam B y) : Bd lam B (x + y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  lift x to Qbar using hx
  lift y to Qbar using hy
  rw [lamC_coe] at h1 h2
  have := Bd.coe (lam := lam) (B := B) (x := x + y) (by
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2))
  simpa using this

theorem Bd.mul {A B : ℝ} {x y : ℂ} (hx : Bd lam A x) (hy : Bd lam B y) : Bd lam (A * B) (x * y) := by
  obtain ⟨hx, h1⟩ := hx
  obtain ⟨hy, h2⟩ := hy
  lift x to Qbar using hx
  lift y to Qbar using hy
  rw [lamC_coe] at h1 h2
  have := Bd.coe (lam := lam) (B := A * B) (x := x * y) (by
    rw [map_mul, norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))
  simpa using this

theorem Bd.sum {ι : Type*} {B : ℝ} (hB : 0 ≤ B) (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, Bd lam B (f i)) :
    Bd lam B (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd lam B) (fun _ _ => Bd.add) (Bd.zero hB) h

theorem Bd.intCast (z : ℤ) : Bd lam 1 (z : ℂ) := by
  have := Bd.coe (lam := lam) (B := 1) (x := (z : Qbar)) (by
    rw [map_intCast]
    exact IsUltrametricDist.norm_intCast_le_one _ z)
  simpa using this

theorem Bd.prod_coe {n : ℕ} {A : ℝ} (c : Fin n → Qbar) (h : ∀ i, ‖lam (c i)‖ ≤ A) :
    Bd lam (A ^ n) (∏ i, (c i : ℂ)) := by
  have := Bd.coe (lam := lam) (B := A ^ n) (x := ∏ i, c i) (by
    rw [map_prod, norm_prod]
    calc ∏ i, ‖lam (c i)‖ ≤ ∏ _i : Fin n, A :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h i)
      _ = A ^ n := by simp)
  simpa using this

theorem bd_applyAt0 (D : D7) {a d n : ℕ} {B : ℝ} (hB : 0 ≤ B) (G : VC D a d → ℂ)
    (P : MvPolynomial (GL3Theta.Idx D a d) ℤ) (hP : P.IsHomogeneous n)
    (h : ∀ f : Fin n → GL3Theta.Idx D a d, Bd lam B (iteratedFDeriv ℂ n G 0 (fun i => coordV D (f i)))) :
    Bd lam B (GL3Theta.applyAt0 D (MvPolynomial.map (Int.castRingHom ℂ) P) G) := by
  have h' : ∀ m, m = n → ∀ f : Fin m → GL3Theta.Idx D a d,
      Bd lam B (iteratedFDeriv ℂ m G 0 (fun i => coordV D (f i))) := by
    rintro m rfl; exact h
  refine Bd.sum hB _ _ fun α hα => ?_
  have hα' : AddMonoidAlgebra.coeff P α ≠ 0 :=
    MvPolynomial.mem_support_iff.1 (MvPolynomial.support_map_subset _ _ hα)
  have hdeg : Multiset.card α.toMultiset = n := by
    have h1 := hP hα'
    rw [Finsupp.card_toMultiset]
    rw [← h1, Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [taylor, mul_assoc, mul_div_cancel₀ _ hne, MvPolynomial.coeff_map]
  have := (Bd.intCast (lam := lam) (AddMonoidAlgebra.coeff P α)).mul (h' _ hdeg
    (fun i => α.toMultiset.toList.get ⟨i, by simpa using i.2⟩))
  rw [one_mul] at this
  exact this

theorem bd_coord (D : D7) {a d n : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (T : Tor D) (hT : ∀ τ x, T.emb τ x = embT D τ x)
    (Y : Set (Matrix (Fin d) (Fin a) D.host.E))
    (hL : ∀ k : GL3Theta.Idx D a d, ∃ (m : ℕ) (c : Fin m → Qbar) (y : Fin m → Matrix (Fin d) (Fin a) D.host.E),
        (∀ i, y i ∈ Y) ∧ (∀ i, ‖lam (c i)‖ ≤ A) ∧
        coordV D k = ∑ i, (c i : ℂ) • (fun τ s t => embT D τ (y i s t) : VC D a d))
    (φ : ContinuousMultilinearMap ℂ (fun _ : Fin n => VC D a d) ℂ)
    (h : ∀ y : Fin n → Matrix (Fin d) (Fin a) D.host.E, (∀ i, y i ∈ Y) → Bd lam B (φ fun i => embV D T (y i)))
    (f : Fin n → GL3Theta.Idx D a d) : Bd lam (A ^ n * B) (φ fun i => coordV D (f i)) := by
  choose m c y hy hc he using hL
  have h1 : (fun i => coordV D (f i)) = fun i => ∑ j, (c (f i) j : ℂ) • embV D T (y (f i) j) := by
    funext i
    rw [he]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext τ s t
    simp [embV, hT]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, φ.map_sum]
  refine Bd.sum (by positivity) _ _ fun r _ => ?_
  rw [φ.map_smul_univ, smul_eq_mul]
  exact (Bd.prod_coe (fun i => c (f i) (r i)) fun i => hc _ _).mul (h _ fun i => hy _ _)

end

def minorZ (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : MvPolynomial (GL3Theta.Idx D a d) ℤ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
    (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℤ)).det

theorem map_minorZ (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    MvPolynomial.map (Int.castRingHom ℂ) (minorZ D T) = minorPol D T := by
  simp only [minorZ, minorPol, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext i i' : 2
  simp

theorem minorZ_homogeneous (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    (minorZ D T).IsHomogeneous (a * ∑ τ, n τ) := by
  have h : a * ∑ τ, n τ = ∑ τ, ∑ _j : Fin (n τ), a := by
    simp [Finset.mul_sum, mul_comm]
  rw [h]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ => MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h2 := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin a))
    (fun i => (MvPolynomial.X (τ, (T τ j).1 (σ i), i) : MvPolynomial (GL3Theta.Idx D a d) ℤ)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X _ _)
  have h3 := (MvPolynomial.isHomogeneous_C (GL3Theta.Idx D a d) ((Equiv.Perm.sign σ : ℤˣ) : ℤ)).mul h2
  simpa using h3

theorem differentiable_evenTheta (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (h : Crv D cc δ) :
    Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ h
  have hs : Differentiable ℂ (sgStar (lamOf D cc δ)) := by
    refine (GlobalTheory.OddTheta.sgStar_laws _ ⟨L.ω₁, L.ω₂, L.indep, ?_⟩).1.1
    ext z
    rw [hL, PeriodPair.lattice, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  unfold GL3Theta.th0 U1
  fun_prop

theorem contDiff_U_pullB (D : D7) (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (s : VC D a d) (n : ℕ) : ContDiff ℂ n (U D T s (pullB D T b g)) := by
  have hg' : ContDiff ℂ n g := hg.contDiff
  have h1 : ContDiff ℂ n (pullB D T b g) := by
    unfold pullB coordB
    refine contDiff_prod fun j _ => ?_
    fun_prop
  unfold U Hf
  fun_prop

theorem norm_natCast_inv (p : ℕ) [Fact p.Prime] {Q : ℕ} (hQ : Q ≠ 0) :
    ‖(Q : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
  have h1 : (Q : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (Q : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hQ), Padic.valuation_natCast]
  simp [Nat.padicValNat_def]

theorem iteratedFDeriv_comb {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} (n : ℕ)
    (r : Fin k → ℂ) (G : Fin k → V → ℂ) (hG : ∀ i, ContDiff ℂ n (G i)) (y : Fin n → V) :
    iteratedFDeriv ℂ n (fun z => ∑ i, r i * G i z) 0 y = ∑ i, r i * iteratedFDeriv ℂ n (G i) 0 y := by
  have h1 : (fun z => ∑ i, r i * G i z) = ∑ i, r i • G i := by
    funext z; simp
  rw [h1, iteratedFDeriv_sum_apply (f := fun i => r i • G i) (fun i _ => ((hG i).const_smul (r i)).contDiffAt),
    sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hG i).contDiffAt, smul_apply, smul_eq_mul]

theorem rpow_collect {x : ℝ} (hx : 0 < x) (c : Prop) [Decidable c] (n m : ℕ) (u v : ℝ) :
    (x ^ u) ^ n * ((x ^ v) ^ m * ((x ^ v) ^ n * (if c then x ^ ((n : ℝ) / 4) else 1))) =
      x ^ ((n : ℝ) * (u + (if c then 1 / 4 else 0) + v) + (m : ℝ) * v) := by
  have he' : (if c then x ^ ((n : ℝ) / 4) else 1) = x ^ ((n : ℝ) * (if c then 1 / 4 else 0)) := by
    split_ifs
    · congr 1; ring
    · simp
  rw [he', ← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le, ← Real.rpow_mul_natCast hx.le,
    ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem term_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∀ T, P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  intro D hI S dl hL δ t0 Q hC ht hQ P p _ lam g g' k' hk hg hg' T
  obtain ⟨b, k, M, r, s, hb, hloc, hM, hMp, hs, hr, hF⟩ :=
    _root_.GlobalTheory.NormSum.kernel_eq_sum_translates D hI δ t0 Q hC ht hQ.1 P p lam g g' k' hk hg hg'
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQn := norm_natCast_inv p hQ.1.ne'
  have hN : ‖((M * Q : ℕ) : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
    have hval : padicValNat p M = 0 := by
      simpa only [Nat.padicValNat_def] using
        (multiplicity_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 hMp.symm))
    rw [norm_natCast_inv p (Nat.mul_pos hM hQ.1).ne', (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hM.ne' hQ.1.ne',
      hval, zero_add]
  have hsp : p ∣ M * Q → SplitIn D p := fun h =>
    hQ.2 p hp (hMp.symm.dvd_of_dvd_mul_left h)
  have he0 : 0 ≤ (if p = D.host.d then (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) / 4) else 1) := by
    split_ifs <;> positivity
  rw [← rpow_collect hp0, Pair.term, ← map_minorZ, hF]
  refine bd_applyAt0 (lam := lam) D (by positivity) _ _ (minorZ_homogeneous D T) fun f => ?_
  refine bd_coord D (by positivity) (by positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D P.a) (stdL D P.d)) (hL.2.2.2.2 p lam P.a P.d) _ (fun y hy => ?_) f
  rw [iteratedFDeriv_comb _ (fun i => (r i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))) fun i =>
    contDiff_U_pullB D _ b _ (differentiable_evenTheta D ⊤ δ t0 hC) (s i) _]
  refine Bd.sum (by positivity) _ _ fun i _ => ?_
  have h1 := hr i
  rw [hQn] at h1
  refine (Bd.coe h1).mul ?_
  have := _root_.GlobalTheory.ProductJets.jets_translate_product D hI p lam ⊤ δ hC (by simp) t0 ht P.a P.d _ b hb hloc (s i) (M * Q)
    (Nat.mul_pos hM hQ.1) (hs i) hsp _ y hy
  rw [hN] at this
  exact this

end GlobalTheory.NormSum.Term
end
end

