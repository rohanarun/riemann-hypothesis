module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaTorsionTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem sqAt_nonneg {X : Fields} {n : ℕ} (lam : X.Tau → DomWeight n) (σ : X.K →+* ℂ) (x : Formalism.L2.DIV.VV X.K lam) :
    0 ≤ sqAt σ lam x := by
  rw [← (_root_.GlobalTheory.ColNorms.gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb n lam σ).2 x]
  have h := (_root_.GlobalTheory.ColNorms.gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb n lam (InfinitePlace.mk σ).embedding).1.dotProduct_mulVec_nonneg
    fun i => (InfinitePlace.mk σ).embedding ((bVV X.K lam).repr x i)
  refine le_of_le_of_eq (Complex.le_def.1 h).1 ?_
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Matrix.of_apply, Pi.star_apply, mul_assoc]
  rfl

theorem sqAt_smul {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (σ : K →+* ℂ) (a : K)
    (x : Formalism.L2.DIV.VV K lam) : sqAt σ lam (a • x) = ‖σ a‖ ^ 2 * sqAt σ lam x := by
  unfold sqAt
  rw [← Complex.re_ofReal_mul]
  congr 1
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : ((‖σ a‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (σ a) * σ a := by
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [h]
  ring

theorem jetOp_sum {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (n : ι → ℕ) {α : Type} (R : Finset α) (c : α → K) (J : α → (DVar ι a b →₀ ℕ) → K) :
    jetOp lam lam' (fun m => ∑ x ∈ R, c x * J x m) n = ∑ x ∈ R, c x • jetOp lam lam' (J x) n := by
  have h : jetLin (fun m => ∑ x ∈ R, c x * J x m) = ∑ x ∈ R, c x • jetLin (K := K) (J x) := by
    refine (MvPolynomial.basisMonomials _ K).ext fun m => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [jetLin, Module.Basis.constr_basis, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [jetOp, jetMap, h, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]

theorem jetC_const_mul {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (κ : ℂ) (F : VCx ι a b → ℂ)
    (h : Differentiable ℂ fun z => κ * F z) (m : DVar ι a b →₀ ℕ) : jetC cD (fun z => κ * F z) m = κ * jetC cD F m := by
  by_cases hκ : κ = 0
  · have := _root_.GlobalTheory.ColNorms.jetC_sum_mul ι a b cD Unit ∅ (fun _ => 0) (fun _ => F) (by simp) m
    simpa [hκ] using this
  · have hF : Differentiable ℂ F := by
      have := h.const_mul κ⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hκ] using this
    have := _root_.GlobalTheory.ColNorms.jetC_sum_mul ι a b cD Unit {()} (fun _ => κ) (fun _ => F) (fun _ _ => hF) m
    simpa using this

theorem cj_coe (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : M) : StandardLatticesGL3.cj M ρ (x : ℂ) = ρ x := by
  unfold StandardLatticesGL3.cj TaylorLogMetric.liftM
  rw [dif_pos x.2]

theorem toHost_back {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) :
    (fun z : VCx X.Tau a b => toHost s F fun τ => z (s.iT.symm τ)) = F := by
  funext z
  simp [toHost]

theorem diff_back {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : TaylorLogMetric.VC D a b → ℂ) (h : Differentiable ℂ F) :
    Differentiable ℂ fun z : VCx X.Tau a b => F fun τ => z (s.iT.symm τ) := by
  refine h.comp ?_
  fun_prop

theorem block : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (t0 : ℂ), X.Ok → s.Ok → StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → (∀ τ, cD τ ≠ 0) → ∀ (a b : ℕ), a < b → Even (a * b) → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) (B.thZero a b) → ∀ (lam nu : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → ∀ (S SB : Finset (HeightOneSpectrum (𝓞 X.E))) (cA c c' : ℕ), 0 < cA → 0 < c → 0 < c' → (ambOf s B χ cD).IndAdd a b S (cA * (c * c')) → JetsInField (ambOf s B χ cD) a b S (cA * (c * c')) (fun τ => ∑ i, (nu τ).w i) → ∀ (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K) (L : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB), IsSdLat L → IsSdLat L' → ∀ (Ξ : HomE X.E a b → X.K) (β : ℝ), SmallDatum S L L' c Ξ β → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hK : ∀ k, s.σ₀ k ∈ M) (ρ : M →ₐ[ℚ] ℂ), TaylorLogMetric.DataIn D B.tor M → (∀ τ, cD τ ∈ M) → TaylorLogMetric.CoefIn D (B.thZero a b) M → ‖((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hK)) (muInvDet sel SB mU mI L fr * (muInvDet sel SB mU mI L' fr')⁻¹)‖ ≤ 1 → CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hK)) lam lam' (kerOf (thDistC (ambOf s B χ cD) S SB (cA * (c * c')) sel mU mI lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) S cA (c * c') L fr L' fr' Ξ) (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax b nu (β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b)) * Real.sqrt (supConst D a b) * Real.exp (logThAt B M ρ a b / 2)) fun τ => Real.exp (logOmAt B cD M ρ (s.iT τ))) := by
  intro hB D X s cc dl B χ cD t0 hX hs hcrv ht0 hc0 a b hab hev hE0 lam nu lam' hst S SB cA c c' hcA hc hc' hInd hJ sel mU mI
    L fr L' fr' hL hL' Ξ β hΞ M _ hK ρ hD hcM hco hsc
  classical
  set A := ambOf s B χ cD with hA
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hK) with hσ
  set κ := (A.chiF a b L L')⁻¹ with hκ
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hΞ.2.2 σ 0)
  obtain ⟨sd0, sdL⟩ := _root_.GlobalTheory.SeamSelfDual.seam_selfDual D X s hs a
  obtain ⟨sd0', sdL'⟩ := _root_.GlobalTheory.SeamSelfDual.seam_selfDual D X s hs b
  have hmv := _root_.GlobalTheory.MovedVacuum.isVacuum_movedThetaVacuum D cc dl B t0 hcrv ht0 a b _ _ (sdL L hL) (sdL' L' hL') hE0
  obtain ⟨ρ', hρ', hlam, harea, hnorm⟩ := _root_.GlobalTheory.ConjVacuumNorm.exists_extension_normSq_eq D cc dl t0 hcrv ht0 M ρ hD
  have hnorm' := hnorm a b _ _ _ _ (sdL L hL) (sdL' L' hL') sd0 sd0' hev _ _ hmv hE0 hco
  have hdiff : ∀ (c₁ : ℕ) (x : HomE X.E a b), 0 < c₁ → Differentiable ℂ fun z => κ * A.thInd S L L' c₁ x z := by
    intro c₁ x h₁
    have h2 := (_root_.GlobalTheory.ConjComb.conj_pres D cc dl t0 hcrv ht0 a b _ _ (sdL L hL) (sdL' L' hL') hev _ _ _ hmv
      (_root_.GlobalTheory.ColNorms.IndPres.pres_thInd D X s cc dl B χ cD hX hs hcrv a b S L L' c₁ x hL hL' h₁) ρ').1
    have h3 := diff_back s _ h2
    rwa [toHost_back] at h3

  haveI := (_root_.GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' cA (c * c') hL.1 hL'.1 hcA (Nat.mul_pos hc hc')).1
  let Qt := ↥(divLat cA (homAt S L L')) ⧸ (mulLat (c * c') (homAt S L L')).comap (divLat cA (homAt S L L')).subtype
  letI : Fintype Qt := Fintype.ofFinite Qt
  let rep : Qt → ↥(divLat cA (homAt S L L')) := Function.surjInv (Submodule.Quotient.mk_surjective _)
  have hsum : ∀ {Y : Type} [AddCommMonoid Y] (f : HomE X.E a b → Y),
      latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) f = ∑ q : Qt, f (rep q) := fun f =>
    finsum_eq_sum_of_fintype _
  have hrep : ∀ q, ((rep q : HomE X.E a b)) ∈ divLat (cA * (c * c')) (homAt S L L') := by
    intro q
    have h1 : ((cA : ℕ) : 𝓞 X.E) • (rep q : HomE X.E a b) ∈ homAt S L L' := (rep q).2
    show (((cA * (c * c') : ℕ)) : 𝓞 X.E) • (rep q : HomE X.E a b) ∈ homAt S L L'
    rw [mul_comm cA, Nat.cast_mul, mul_smul]
    exact Submodule.smul_mem _ _ h1
  let J : (DVar X.Tau a b →₀ ℕ) → X.K := fun m => ∑ q : Qt, Ξ (rep q) * A.jetK S L L' (c * c') (rep q) m
  have hker : kerOf (thDistC A S SB (cA * (c * c')) sel mU mI lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ)) S cA (c * c')
      L fr L' fr' Ξ = (muInvDet sel SB mU mI L fr * (muInvDet sel SB mU mI L' fr')⁻¹) •
        jetOp lam lam' J fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
    unfold kerOf
    rw [hsum, jetOp_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold thDistC
    rw [if_pos ⟨Dvd.intro_left _ rfl, hrep q⟩, smul_comm]

  let F : VCx X.Tau a b → ℂ := fun z => ∑ q : Qt, s.σ₀ (Ξ (rep q)) * (κ * A.thInd S L L' (c * c') (rep q) z)
  have hJF : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) → s.σ₀ (J e) = jetC A.cD F e := by
    intro e he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [_root_.GlobalTheory.ColNorms.jetC_sum_mul X.Tau a b A.cD Qt Finset.univ _ _ (fun q _ => hdiff _ _ (Nat.mul_pos hc hc')) e, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, jetC_const_mul _ _ _ (hdiff _ _ (Nat.mul_pos hc hc'))]
    congr 1
    have h1 := hJ L L' (c * c') (rep q) ⟨hL, hL', Nat.mul_pos hc hc', Dvd.intro_left _ rfl, hrep q⟩ e (fun τ => by
      refine Eq.trans ?_ (he τ)
      unfold degAt
      congr)
    unfold Amb.jetK desc
    rw [dif_pos h1]
    exact h1.choose_spec
  obtain ⟨R, hRc, hR⟩ := _root_.GlobalTheory.latSum_thInd_regroup X A a b S L L' cA c c' (fun x => s.σ₀ (Ξ x)) hInd hL hL' hcA hc hc'
    (fun x hx => hΞ.1 x fun h => hx (by rw [h, map_zero])) (fun x y hy => by rw [hΞ.2.1 x y hy])
  have hF : toHost s F = fun w => ∑ x ∈ R, s.σ₀ (Ξ x) * toHost s (fun z => κ * A.thInd S L L' c x z) w := by
    funext w
    have h1 := hR fun τ => w (s.iT τ)
    rw [hsum] at h1
    show ∑ q : Qt, s.σ₀ (Ξ (rep q)) * (κ * _) = ∑ x ∈ R, s.σ₀ (Ξ x) * (κ * _)
    simp only [mul_left_comm _ κ, ← Finset.mul_sum]
    exact congrArg _ h1
  have hKQ : ∀ k, s.σ₀ k ∈ TaylorLogMetric.Qbar := fun k => (hρ' _ (hK k)).1
  have hpres := _root_.GlobalTheory.PresSum.pres_sum D (TaylorLogMetric.tor0 D cc dl) a b (s.lat L) (s.lat L') _ _ R (fun x => s.σ₀ (Ξ x)) _ _ β hβ
    (fun x _ => _root_.GlobalTheory.ColNorms.IndPres.pres_thInd D X s cc dl B χ cD hX hs hcrv a b S L L' c x hL hL' hc)
    (fun x _ => ⟨hKQ _, fun ρ₁ => by
      have h1 := hΞ.2.2 ((ρ₁ : TaylorLogMetric.Qbar →+* ℂ).comp (s.σ₀.codRestrict TaylorLogMetric.Qbar hKQ)) x
      have h2 := cj_coe TaylorLogMetric.Qbar ρ₁ ⟨s.σ₀ (Ξ x), hKQ _⟩
      exact h2 ▸ h1⟩)
  rw [← hF] at hpres
  obtain ⟨hFd, hFQ, F', hF'd, hF't, hF'b⟩ := _root_.GlobalTheory.ConjComb.conj_pres D cc dl t0 hcrv ht0 a b _ _ (sdL L hL) (sdL' L' hL') hev _ _ _ hmv hpres ρ'
  rw [hnorm', hlam] at hF'b
  set ar := TaylorLogMetric.area (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc dl)) with har
  let cD' : X.Tau → ℂ := fun τ => ρ (TaylorLogMetric.liftM M (cD (s.iT τ)))
  have hcD' : ∀ τ, cD' τ ≠ 0 := fun τ => by
    have h1 : TaylorLogMetric.liftM M (cD (s.iT τ)) = ⟨cD (s.iT τ), hcM _⟩ := dif_pos (hcM _)
    show ρ _ ≠ 0
    rw [h1, map_ne_zero]
    exact fun h => hc0 _ (congrArg Subtype.val h)
  have hJ' : ∀ e, (∀ τ, ((degAt e τ : ℕ) : ℤ) = ∑ i, (nu τ).w i) →
      σ (J e) = jetC cD' (fun z : VCx X.Tau a b => F' fun τ => z (s.iT.symm τ)) e := by
    intro e he
    have h1 : σ (J e) = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ' (s.σ₀ (J e)) := by
      rw [(hρ' _ (hK _)).2]
      exact (cj_coe M ρ ⟨_, hK _⟩).symm
    rw [h1, hJF e he, ← toHost_back s F]
    unfold jetC
    rw [_root_.GlobalTheory.DerivReindex.derivAt0_reindex D X.Tau s.iT a b _ hFd, _root_.GlobalTheory.DerivReindex.derivAt0_reindex D X.Tau s.iT a b _ hF'd, hF't]
    have hq : ∀ τ, cD (s.iT τ) ∈ TaylorLogMetric.Qbar := fun τ => (hρ' _ (hcM _)).1
    have h2 := cj_coe TaylorLogMetric.Qbar ρ' ((e.prod fun k n => (⟨cD (s.iT k.1), hq _⟩ : TaylorLogMetric.Qbar) ^ n) *
      ((e.prod fun _ n => (n.factorial : TaylorLogMetric.Qbar)) * ⟨_, hFQ (Finsupp.equivMapDomain (s.iT.prodCongr (Equiv.refl (Fin b × Fin a))) e)⟩))
    have h3 : ∀ τ, ρ' ⟨cD (s.iT τ), hq τ⟩ = cD' τ := fun τ => (cj_coe TaylorLogMetric.Qbar ρ' ⟨_, hq τ⟩).symm.trans (hρ' _ (hcM _)).2
    refine Eq.trans (congrArg _ ?_) (h2.trans ?_)
    · simp only [Finsupp.prod, IntermediateField.coe_mul, IntermediateField.coe_prod, IntermediateField.coe_pow]
      simp [hA, ambOf]
    · simp only [Finsupp.prod, map_mul, map_prod, map_pow, map_natCast, h3]
      rw [← cj_coe TaylorLogMetric.Qbar ρ']
  have hr : 0 < Real.pi / ar := div_pos Real.pi_pos harea
  have hblock := hB X.Tau a b hab.le lam nu lam' hst (fun h => absurd h hab.ne) (fun _ => Real.sqrt (Real.pi / ar))
    (fun τ => Real.exp (logOmAt B cD M ρ (s.iT τ))) cD' (fun _ => Real.sqrt_pos.2 hr) (fun _ => Real.exp_pos _) (fun τ => by
      have h1 : 0 < ‖cD' τ‖ := norm_pos_iff.2 (hcD' τ)
      unfold logOmAt TaylorLogMetric.logMet
      rw [Real.exp_neg, one_div, inv_inv, Real.exp_log (by show 0 < Real.pi * ‖cD' τ‖ ^ 2 / ar; positivity), norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hr.le]
      show _ = Real.pi * ‖cD' τ‖ ^ 2 / ar
      ring)
    (fun z : VCx X.Tau a b => F' fun τ => z (s.iT.symm τ))
    (β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b)) * Real.sqrt (supConst D a b) * Real.exp (logThAt B M ρ a b / 2))
    (diff_back s _ hF'd) (fun z => by
      have hsup : 0 ≤ supConst D a b := by
        unfold supConst Host.rdE
        positivity
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      refine (hF'b _).trans ?_
      have e1 : Real.pi * (∑ τ, ∑ i, ∑ j, ‖z (s.iT.symm τ) i j‖ ^ 2) / ar =
          GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.unitSq (fun _ => Real.sqrt (Real.pi / ar)) z := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.unitSq
        rw [s.iT.symm.sum_comp fun τ => ∑ i, ∑ j, ‖z τ i j‖ ^ 2]
        simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hr.le, ← Finset.mul_sum]
        ring
      have e2 : ∀ y : ℝ, Real.exp (y / 2) ^ 2 = Real.exp y := fun y => by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have b1 : (R.card : ℝ) * β * (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) ≤ β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b)) := by
        have h1 : (R.card : ℝ) ≤ (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) := by exact_mod_cast hRc
        calc _ ≤ (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) * β * (c : ℝ) ^ (Module.finrank ℚ X.E * a * b) := by gcongr
          _ = _ := by ring
      have b2 := Real.le_exp_log (TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ)
        (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) M ρ) (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)) (TaylorLogMetric.fnConj D M ρ (B.thZero a b)))
      rw [e1]
      calc _ ≤ (β * (c : ℝ) ^ (2 * (Module.finrank ℚ X.E * a * b))) ^ 2 * (supConst D a b * Real.exp (logThAt B M ρ a b) *
            Real.exp (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.unitSq (fun _ => Real.sqrt (Real.pi / ar)) z)) := by
            refine mul_le_mul (pow_le_pow_left₀ (by positivity) b1 2) ?_ ?_ (by positivity)
            · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 hsup) (Real.exp_pos _).le
            · refine mul_nonneg (mul_nonneg hsup ?_) (Real.exp_pos _).le
              unfold TaylorLogMetric.normSq
              exact MeasureTheory.integral_nonneg fun _ => by positivity
        _ = _ := by
            rw [mul_pow _ (Real.exp _), mul_pow _ (Real.exp _), mul_pow _ (Real.sqrt _), e2, e2, Real.sq_sqrt hsup]
            ring)
  have hbc := _root_.GlobalTheory.coefOpLe_jetOp_of_opNormSqLe X.K σ X.Tau a b lam nu lam' hst (_root_.GlobalTheory.ColNorms.jetInVV_of_stepWeights X.K X.Tau a b hab lam nu lam' hst)
    (_root_.GlobalTheory.ColNorms.jetInVV_of_stepWeights ℂ X.Tau a b hab lam nu lam' hst) J _ hJ' _ hblock
  intro x
  rw [hker, LinearMap.smul_apply, sqAt_smul]
  refine le_trans ?_ (hbc x)
  refine mul_le_of_le_one_left (sqAt_nonneg _ _ _) ?_
  exact pow_le_one₀ (norm_nonneg _) hsc

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdeal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelMoveCong

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem intAdele_smul_mem_hat {n : ℕ} (S : Set (Fin n → E)) (c : FiniteAdeleRing (𝓞 F) F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F S) : (c ⊗ₜ[F] (1 : E)) • z ∈ GlobalTheory.AdLat.hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem ideal_smul_mem_hat {n : ℕ} (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) {t : 𝓞 E} (ht : t ∈ I)
    {z : Fin n → GlobalTheory.AdLat.RA F E} (hz : z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E)) • z ∈
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, t • x, Submodule.smul_mem_smul ht hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem nsmul_eq_smul {n : ℕ} (M : ℕ) (w : Fin n → GlobalTheory.AdLat.RA F E) :
    M • w = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((M : 𝓞 E) : E))) • w := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, map_natCast]
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem split_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (x y : Fin n → GlobalTheory.AdLat.RA F E)
    (r : GlobalTheory.AdLat.RA F E) (h : x = y + r • x) :
    K *ᵥ x - x = (K *ᵥ y - y) + r • (K *ᵥ x - x) := by
  conv_lhs => rw [h]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem gen_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (c : FiniteAdeleRing (𝓞 F) F)
    (x : Fin n → E) :
    K *ᵥ (fun i => c ⊗ₜ[F] x i) - (fun i => c ⊗ₜ[F] x i) =
      (c ⊗ₜ[F] (1 : E)) • (K *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x) := by
  have e : (fun i => c ⊗ₜ[F] x i) = (c ⊗ₜ[F] (1 : E)) • GlobalTheory.AdLat.fv F x := by
    funext i; simp [GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, Matrix.mulVec_smul, smul_sub]

end Gen

end GlobalTheory.LevelMoveCong

namespace GlobalTheory.LevelMoveCong

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix


set_option maxHeartbeats 2000000 in
theorem mulVec_sub_mem_hat_smul : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V La _ _ ι hι M Mb Mh hsup hM κ hκ f hf hfb z hz
  set K := (Formalism.L2.Theta.finHom V κ).1 with hKdef
  set L' := Formalism.L2.Pj.latG V 1 with hL'
  set P := GlobalTheory.AdLat.hat D.host.F ((Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    Set (Fin V.rank → D.host.E)) with hP
  have hhat1 : Formalism.L2.Pj.latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  have hK : ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)),
      K *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) := by
    intro y hy
    have h4 := (GlobalTheory.Member.latG_lattice_and_completion D V κ).2.2.2.1
    have he := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hκ
    have h5 : K *ᵥ y ∈ (Formalism.L2.Pj.latGHat V κ : Set _) := by rw [h4]; exact ⟨y, hy, rfl⟩
    rw [he, hhat1] at h5
    exact h5
  have hone : ∀ v, (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) v ∈ v.adicCompletionIntegers D.host.F :=
    fun v => one_mem _
  have hfv : ∀ u ∈ L', Formalism.L2.Pj.finVec V u ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  have hfvP : ∀ u ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.Pj.finVec V u ∈ P :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  obtain ⟨b, hb, m, hm, hmb⟩ : ∃ b ∈ Mb, ∃ m ∈ Mh, b + m = 1 :=
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hfv_sub : ∀ u u', Formalism.L2.Pj.finVec V (u - u') = Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u' := by
    intro u u'; funext i; simp [Formalism.L2.Pj.finVec, TensorProduct.tmul_sub]
  have hrange : ∀ x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La),
      ι x ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
    intro x hx
    have h1 : ι x ∈ (Mb • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := Submodule.mem_map_of_mem hx
    rwa [Submodule.map_smul'', Submodule.map_top, hι.2] at h1

  have step1 : ∀ v : La, K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) ∈ P := by
    intro v
    obtain ⟨w, hw, hw'⟩ := hf (m • v) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have e : K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) =
        Formalism.L2.Pj.finVec V (ι (f (m • v) - m • v)) - M • w := by
      rw [map_sub, hfv_sub, ← hw']; abel
    rw [e]
    refine sub_mem (hfvP _ (hrange _ (hfb _))) ?_
    rw [hhat1] at hw
    rw [nsmul_eq_smul]
    exact ideal_smul_mem_hat Mb L' hM hw

  have step2 : ∀ u ∈ L', K *ᵥ Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u ∈ P := by
    intro u hu
    have hu' : u ∈ LinearMap.range ι := by rw [hι.2]; exact hu
    obtain ⟨v, rfl⟩ := hu'
    have hsplit : Formalism.L2.Pj.finVec V (ι v) = Formalism.L2.Pj.finVec V (ι (m • v)) +
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) •
          Formalism.L2.Pj.finVec V (ι v) := by
      funext i
      simp only [Formalism.L2.Pj.finVec, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_add]
      congr 1
      rw [Algebra.smul_def, ← add_mul]
      have : ((algebraMap (𝓞 D.host.E) D.host.E m) + (b : D.host.E)) = 1 := by
        show ((m : D.host.E)) + (b : D.host.E) = 1
        rw [add_comm]; exact_mod_cast congrArg ((↑) : 𝓞 D.host.E → D.host.E) hmb
      rw [this, one_mul]
    rw [split_sub K _ _ _ hsplit]
    refine add_mem (step1 v) (ideal_smul_mem_hat Mb L' hb ?_)
    have hu : ι v ∈ L' := by rw [hL', ← hι.2]; exact ⟨v, rfl⟩
    exact sub_mem (hK _ (hfv _ hu)) (hfv _ hu)

  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    rw [gen_sub K c x]
    exact intAdele_smul_mem_hat _ c hc (step2 x hx)
  | zero => rw [Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add y y' _ _ h h' =>
    have e : K *ᵥ (y + y') - (y + y') = (K *ᵥ y - y) + (K *ᵥ y' - y') := by
      rw [Matrix.mulVec_add]; abel
    rw [e]; exact add_mem h h'
  | neg y _ h =>
    have e : K *ᵥ (-y) - (-y) = -(K *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [e]; exact neg_mem h

end GlobalTheory.LevelMoveCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isOn_pull_comp : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z),
    IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  intro X Z Z' W L r s hL hr
  have h : (L.pull (s ≫ r)).IsLB := _root_.GlobalTheory.PicGlue.pull_isLB_of_isOn X Z' W L (s ≫ r) hL fun z ↦ by
    simpa using hr (s z)
  exact iso_of_chart h (chartPullLinComb L r (fun _ : PUnit => s) (fun _ => s ≫ r) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm)

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
section
noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_mul {T L : Subgroup H} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : GlobalTheory.LKLoc.locPart T L (t * x * l) = GlobalTheory.LKLoc.locPart T L x := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩
    calc x * (l * k * l⁻¹) * x⁻¹ = t⁻¹ * ((t * x * l * k * (t * x * l)⁻¹) * t) := by group
      _ = t⁻¹ * (t * (t * x * l * k * (t * x * l)⁻¹)) := by rw [hT _ hg t ht]
      _ = t * x * l * k * (t * x * l)⁻¹ := by group
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩
    have := hT _ hg t ht
    calc t * x * l * (l⁻¹ * k * l) * (t * x * l)⁻¹ = t * (x * k * x⁻¹) * t⁻¹ := by group
      _ = (x * k * x⁻¹) * t * t⁻¹ := by rw [← this]
      _ = x * k * x⁻¹ := by group

theorem wt_mul {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : wt T L U Ψ (t * x * l) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_mul hT ht hl, hΨr l hl, hΨl t ht]

theorem wt_out {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) (x : H) :
    wt T L U Ψ (Quotient.out (DoubleCoset.mk T L x)) = wt T L U Ψ x := by
  obtain ⟨t, ht, l, hl, h⟩ := (@DoubleCoset.eq _ _ T L _ _).1 (DoubleCoset.out_eq' (DoubleCoset.mk T L x))
  exact (wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_birigidified_trivial_on_axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  first | (exact @GlobalTheory.AxisPairing.axes) | (exact GlobalTheory.AxisPairing.axes) | (intros; apply GlobalTheory.AxisPairing.axes  <;> assumption)
end

