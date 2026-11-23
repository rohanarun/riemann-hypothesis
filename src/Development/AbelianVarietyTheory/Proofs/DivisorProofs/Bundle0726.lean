module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIsLevelLiftOfPoint
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isLift_of_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (om : ObjMap (o'.forget N hd hc) o f) (T : Over S) (g : T.left ⟶ S') (lv : D.La → (T ⟶ o.A)), g ≫ f = T.hom → (∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ om.φ) → IsLift o N' T lv := by
  intro p _ D R _ b N N' hd hc S S' s s' o o' f om T g lv hT hlv
  obtain ⟨T, ⟨⟨⟩⟩, h⟩ := T
  change T ⟶ S' at g
  replace hT : (g ≫ f : T ⟶ S) = h := hT
  subst hT
  obtain ⟨φ, hφ⟩ : ∃ φ : o'.A.left ⟶ o.A.left, φ = om.φ := ⟨om.φ, rfl⟩
  have hlv' : ∀ a, (lv a).left = g ≫ (o'.eta a).left ≫ φ := fun a => by rw [hφ]; exact hlv a
  have cart : IsGrpPullback o'.A o.A f φ := by rw [hφ]; exact om.cart
  have sq : IsSquare φ om.φ₂ := by rw [hφ]; exact om.sq
  have ha : ∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => by rw [hφ]; exact om.act c
  have he : ∀ x, (o'.eta ((N' / N) • x)).left ≫ φ = f ≫ (o.eta x).left := fun x => by rw [hφ]; exact om.eta x
  let T' : Over S' := Over.mk g
  let q : D.La → (T' ⟶ o'.A) := fun a => toUnit T' ≫ o'.eta a
  have hq : ∀ a, (q a).left = g ≫ (o'.eta a).left := fun a => by
    simp only [q, Over.comp_left, Over.toUnit_left]
    rfl
  have key : ∀ a, (lv a).left = (q a).left ≫ φ := fun a => by rw [hlv', hq, Category.assoc]
  have mulx : ∀ x y : D.La, (lv x * lv y).left = (q x * q y).left ≫ φ := fun x y =>
    cart.2 T' (q x) (q y) (lv x) (lv y) (key x) (key y)
  refine ⟨fun x y => ?_, fun x => ?_, fun c x => ?_, fun x => ?_, fun k _ _ x => ?_⟩
  · apply Over.OverMorphism.ext
    rw [mulx, key]
    congr 1
    show (toUnit T' ≫ o'.eta (x + y)).left = (toUnit T' ≫ o'.eta x * toUnit T' ≫ o'.eta y).left
    rw [o'.eta_add, MonObj.comp_mul]
  · have h1 : q (N' • x) = 1 := by
      show toUnit T' ≫ o'.eta (N' • x) = 1
      rw [o'.eta_ker, MonObj.comp_one]
    have hzz : lv (N' • x) * lv (N' • x) = lv (N' • x) * 1 := by
      rw [_root_.mul_one]
      apply Over.OverMorphism.ext
      rw [mulx, key, h1, _root_.mul_one]
    exact mul_left_cancel hzz
  · apply Over.OverMorphism.ext
    rw [Over.comp_left, hlv', hlv', o'.eta_lin, Over.comp_left]
    simp only [Category.assoc, ha]
  · apply Over.OverMorphism.ext
    rw [hlv', he, Over.comp_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm
  · obtain ⟨I', hI'⟩ := o'.geom k (x ≫ g) (Spec.preimage ((x ≫ g) ≫ s')).hom (Spec.map_preimage _).symm
    have h3 := (_root_.GlobalTheory.UPel.HT.tateIsoO_pullback p D R b N N' S S' s s' o o' f φ om.φ₂ cart sq ha om.pol k (x ≫ g)).1 I'
    rw [Category.assoc] at h3
    obtain ⟨I, hI⟩ := h3
    refine ⟨I, fun y => ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hI, ← hI' y, Over.comp_left, Over.toUnit_left]
    change x ≫ (lv y).left = _
    rw [hlv']
    simp only [Over.mk_hom, Category.assoc]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleModuleInfId
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ.DetSplit

variable {K : Type} [Field K] [NumberField K] [IsTotallyReal K] {n : ℕ}

omit [NumberField K] in
theorem norm_realSymm (w : InfinitePlace K) (r : ℝ) :
    ‖((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r : w.Completion)‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0
  have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0 :=
    map_zero _
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
  exact h

theorem ideleModule_infId (u : (Rinf K)ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (UpperTheory.V.TR.infId K u) : ℝ) = ∏ w, |u.val w| := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).1 = UpperTheory.V.TR.infEq K u.val := by
    show (1 : InfiniteAdeleRing K) - UpperTheory.V.TR.infEq K 1 + UpperTheory.V.TR.infEq K u.val = _
    simp
  have h2 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).2 = 1 := by
    show (1 : Af K) - 0 + 0 = 1
    simp
  rw [h1, h2]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : Af K) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  rw [h3, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact norm_realSymm w (u.val w)

end GlobalTheory.HenQ.DetSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEq
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open GlobalTheory.Published.StrongApprox
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormFin

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  by
  apply RestrictedProduct.ext
  intro w
  exact h w

def iotaL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by change (0 : Ainf F) = 0 + 0; simp) ?_
    change singleV F v (a + b) = singleV F v a + singleV F v b
    refine af_ext fun w => ?_
    rw [map_add (f := _)]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, add_zero]
  map_smul' c a := by
    refine Prod.ext (by change (0 : Ainf F) = c • 0; simp) ?_
    change singleV F v (c • a) = c • singleV F v a
    refine af_ext fun w => ?_
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, smul_zero]

theorem iotaL_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    iotaL v (a * b) = iotaL v a * iotaL v b := by
  refine Prod.ext (by change (0 : Ainf F) = 0 * 0; simp) ?_
  change singleV F v (a * b) = singleV F v a * singleV F v b
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; simp only [evalV_single_same]
  · simp only [evalV_single_ne hw, mul_zero]

theorem idem_mul_iotaL (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (a : Fv F v) :
    ε * iotaL v a = iotaL v a := by
  refine Prod.ext (by change fstA F ε * 0 = 0; simp) ?_
  change sndA F ε * singleV F v a = singleV F v a
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [hε.2.2.1 w (Finset.mem_singleton_self w), one_mul]
  · simp only [evalV_single_ne hw, mul_zero]

theorem iotaL_one (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) :
    iotaL v 1 = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    exact (hε.2.1 w (Finset.notMem_empty w)).symm
  · change singleV F v 1 = sndA F ε
    refine af_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same, hε.2.2.1 w (Finset.mem_singleton_self w)]
    · rw [evalV_single_ne hw, hε.2.2.2 w (fun h => hw (Finset.mem_singleton.1 h))]

section Tensor

variable {E : Type} [Field E] [Algebra F E]

def phi (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (iotaL v) LinearMap.id

theorem phi_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    phi v (a ⊗ₜ[F] e) = iotaL v a ⊗ₜ[F] e := TensorProduct.map_tmul _ _ _ _

theorem phi_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v ⊗[F] E) :
    phi v (x * y) = phi v x * phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, phi_tmul, phi_tmul, phi_tmul, iotaL_mul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [mul_add, map_add (f := _), hy, hz, map_add (f := _), mul_add]
  | add x z hx hz => rw [add_mul, map_add (f := _), hx, hz, map_add (f := _), add_mul]

theorem phi_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    phi v (sigR (Fv F v) σ x) = sigR (AF F) σ (phi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, phi_tmul]
  | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz, map_add (f := _), map_add (f := _)]

theorem idem_mul_phi (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε)
    (x : Fv F v ⊗[F] E) : algebraMap (AF F) (AF F ⊗[F] E) ε * phi v x = phi v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, phi_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, idem_mul_iotaL v ε hε]
  | add x z hx hz => rw [map_add (f := _), mul_add, hx, hz]

theorem phi_inclR (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (c : E) :
    phi v (inclR (Fv F v) c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  change phi v ((1 : Fv F v) ⊗ₜ[F] c) = algebraMap (AF F) (AF F ⊗[F] E) ε * ((1 : AF F) ⊗ₜ[F] c)
  rw [phi_tmul, iotaL_one v ε hε, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Tensor

theorem idem_norm_eq_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E,
    (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ v ε hε c ⟨t, ht⟩
  refine ⟨phi v t, ?_⟩
  rw [← phi_sig, ← phi_mul, mul_add, idem_mul_phi v ε hε, ← phi_inclR v ε hε, ← map_add (f := _), ht, map_zero]

end GlobalTheory.NormFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersLatticeInvariantsNeZero
section
open GlobalTheory.Published Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem isIntegral_sqrtNegNat (p : ℕ) : IsIntegral ℤ (sqrtNegNat p) :=
  IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)

theorem exists_rat_of_mem_adjoin_sqrtNegNat {p : ℕ} {z : ℂ} (hz : z ∈ ℚ⟮sqrtNegNat p⟯) :
    ∃ a b : ℚ, z = a + b * sqrtNegNat p := by
  have hint : IsIntegral ℚ (sqrtNegNat p) := (isIntegral_sqrtNegNat p).tower_top
  have hz' : z ∈ Algebra.adjoin ℚ {sqrtNegNat p} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simpa using hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - p * (b * d), a * d + b * c, by
      push_cast; linear_combination (b * d : ℂ) * sqrtNegNat_sq p⟩

theorem dvd_of_sqrtNegNat_mem {p q : ℕ} (hp : p.Prime) (h : sqrtNegNat q ∈ ℚ⟮sqrtNegNat p⟯) :
    p ∣ q := by
  obtain ⟨a, b, e⟩ := exists_rat_of_mem_adjoin_sqrtNegNat h
  have ha : a = 0 := by
    have := congrArg Complex.re e
    simpa [sqrtNegNat] using this.symm
  have e2 : (q : ℂ) = b ^ 2 * p := by
    have := sqrtNegNat_sq q
    rw [e, ha] at this
    push_cast at this
    linear_combination this - (b : ℂ) ^ 2 * sqrtNegNat_sq p
  have e3 : (q : ℚ) = b ^ 2 * p := by exact_mod_cast e2
  have hs : IsSquare ((q * p : ℕ) : ℚ) := ⟨b * p, by push_cast; rw [e3]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_natCast_iff.1 hs
  have hpn : p ∣ n := by
    have : p ∣ n * n := hn ▸ dvd_mul_left p q
    exact (hp.dvd_mul.1 this).elim id id
  have : p * p ∣ q * p := hn ▸ mul_dvd_mul hpn hpn
  exact Nat.dvd_of_mul_dvd_mul_right hp.pos this

theorem mem_adjoin_of_invariant {p : ℕ} {L : PeriodPair} (hL : IsIntegersLattice p L) (m : ℂ) (hm0 : m ≠ 0)
    (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) : m ∈ ℚ⟮sqrtNegNat p⟯ := by
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)
  have := (H₀ 1).2 ((hL 1).2 ⟨one_mem _, isIntegral_one⟩)
  rw [e, mul_one] at this
  exact ((hL m).1 this).1

theorem integersLattice_invariants_ne_zero :
    ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L →
      L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  intro p L hp h3 hL
  refine ⟨fun h => ?_, fun h => ?_, fun ω hω => ?_⟩
  · have hs := sqrtNegNat_sq 3
    push_cast at hs
    have h6 : ((1 + sqrtNegNat 3) / 2) ^ 3 = -1 := by
      linear_combination (3 / 8 + sqrtNegNat 3 / 8) * hs
    have hm := mem_adjoin_of_invariant hL ((1 + sqrtNegNat 3) / 2)
      (fun e => by rw [e] at h6; norm_num at h6) (by simp [h])
      (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp)
    have hm' : sqrtNegNat 3 ∈ ℚ⟮sqrtNegNat p⟯ := by
      have := sub_mem (add_mem hm hm) (one_mem _)
      convert this using 1
      ring
    exact absurd (Nat.le_of_dvd three_pos (dvd_of_sqrtNegNat_mem hp hm')) (not_le.2 h3)
  · have hm := mem_adjoin_of_invariant hL Complex.I Complex.I_ne_zero (by simp) (by simp [h])
    have hm' : sqrtNegNat 1 ∈ ℚ⟮sqrtNegNat p⟯ := by simpa [sqrtNegNat] using hm
    have := Nat.le_of_dvd one_pos (dvd_of_sqrtNegNat_mem hp hm')
    omega
  · exact (hL _).2 ⟨mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ((hL ω).1 hω).1,
      (isIntegral_sqrtNegNat p).mul ((hL ω).1 hω).2⟩

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
section
noncomputable section

namespace GlobalTheory.ColumnNormCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

@[reducible] def numDatumOfParameters (D : D7) (large₂ : SizeData₂ D) : NumDatum where
  R := D.R
  sc := large₂.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊D.s.Del⌋₊
  h0 := ⌈LevelStarExponents.h0 large₂⌉₊
  hc := fun z => D.hc (tauPl D z)

def plRec (D : D7) : RPl D.R ≃ D.what₂.Tau := GlobalTheory.InertCompare.plEquiv D

def codeRec {D : D7} (large₂ : SizeData₂ D) (u : D.what₂.Word) : Code (numDatumOfParameters D large₂) := D.s.letter u

section Rec

variable {D : D7} (large₂ : SizeData₂ D) {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (eta : Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

end Rec

end GlobalTheory.ColumnNormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LatticeJInt

theorem main : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 →
    _root_.IsIntegral ℤ (latticeCurve L).j := by
  intro L β hβ him
  obtain ⟨c, τ, hτ⟩ := ReciprocityTheory.ChartRestriction.L1.latTau L
  have hj := GlobalTheory.JInt.main L c τ β hτ hβ him
  rw [← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ] at hj
  rw [latticeCurve_j_eq]
  exact hj

end GlobalTheory.CMModel.LatticeJInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfDiscrEqUnitMulNegCube
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem isMinimal_of_discr_eq_unit_mul_neg_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  intro p F _ _ w W u hp hI hΔ
  have hmem : ∀ y : F, y ∈ w.valuationSubringAtPrime F ↔ w.valuation F y ≤ 1 := by
    intro y
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rfl
  refine GlobalTheory.isMinimal_of_forall_div_pow_twelve _ F W hI ?_
  intro x hx0 hx
  by_contra hnu
  have hxF : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hx1 : w.valuation F (x : F) < 1 := by
    refine lt_of_le_of_ne ((hmem _).1 x.2) (fun h => hnu ?_)
    have hi : (x : F)⁻¹ ∈ w.valuationSubringAtPrime F := by
      rw [hmem, map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hxF))
  have hu : w.valuation F ((u : w.valuationSubringAtPrime F) : F) = 1 := by
    have h1 := (hmem _).1 (u : w.valuationSubringAtPrime F).2
    have h2 := (hmem _).1 ((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F).2
    have h3 : w.valuation F ((u : w.valuationSubringAtPrime F) : F) *
        w.valuation F (((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F) : F) = 1 := by
      rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]; simp
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ _ * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  obtain ⟨y, hy⟩ := hx
  have hy1 := (hmem _).1 y.2
  have hyx : (y : F) * (x : F) ^ 12 = W.Δ := by
    have : (y : F) = W.Δ / (x : F) ^ 12 := hy
    rw [this]; field_simp
  have hv := congrArg (w.valuation F) (hyx.trans hΔ)
  rw [map_mul, map_mul, hu, Valuation.map_neg, map_pow, map_pow, one_mul] at hv
  have hpv : w.valuation F (p : F) = w.intValuation (p : 𝓞 F) := by
    rw [← w.valuation_of_algebraMap (K := F)]; simp
  have hp' : WithZero.exp (-(3 : ℤ)) < w.valuation F (p : F) := by
    rw [hpv]
    by_contra h
    exact hp ((w.intValuation_le_pow_iff_mem _ 3).1 (by simpa using h))
  have hle : w.valuation F (p : F) ^ 3 ≤ w.valuation F (x : F) ^ 12 := by
    rw [← hv]
    calc _ ≤ 1 * _ := mul_le_mul_left hy1 _
      _ = _ := one_mul _
  have hvx0 : w.valuation F (x : F) ≠ 0 := by simpa using hxF
  have hvp0 : w.valuation F (p : F) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  rw [← WithZero.exp_log hvx0] at hle hx1
  rw [← WithZero.exp_log hvp0] at hle hp'
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hp'
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx1
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  omega

end GlobalTheory.CMModel
end

