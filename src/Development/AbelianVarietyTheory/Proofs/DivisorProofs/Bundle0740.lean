module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorUnitExponentialEstimate
section
noncomputable section

namespace GlobalTheory.ColNorms.NumMean

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms

theorem log_le_of_le_exp {y X : ℝ} (hy : 0 ≤ y) (hX : 0 ≤ X) (h : y ≤ Real.exp X) : Real.log y ≤ X := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact hX
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_mul_le {h h' : ℕ} {X : ℝ} (hX : 0 ≤ X) (h1 : (h : ℝ) ≤ Real.exp X) (h2 : (h' : ℝ) ≤ Real.exp X) :
    Real.log ((h : ℝ) * h') ≤ 2 * X := by
  refine log_le_of_le_exp (by positivity) (by linarith) ?_
  rw [two_mul, Real.exp_add]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem one_le_rd (N : NumDatum) : 1 ≤ N.rd := by
  have h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2 := N.H.der.rd_sq_ge
  have h0 : (0 : ℝ) ≤ N.rd := by
    unfold NumDatum.rd Formalism.HC.HostRaw.rd
    positivity
  have ho : (1 : ℝ) ≤ N.R.ord := by exact_mod_cast N.R.ord_pos
  nlinarith

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  have := Real.add_one_le_exp s.L
  have := one_le_L s
  unfold Scale.b; linarith

theorem card_RPl (R : Ranks) : (Fintype.card (RPl R) : ℝ) = R.f := by
  have h : Fintype.card R.A = R.ord := R.card_A
  simp [RPl, Ranks.f, Ranks.n, h]

theorem N_le (N : NumDatum) {j : ℕ} (hj : j ≤ N.R.m) : (N.R.N j : ℝ) ≤ N.Nm := by
  have : N.R.N j ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  exact_mod_cast this

theorem log_le_mul (s : Scale) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) (h : y ≤ s.b ^ k) : Real.log y ≤ k * s.L := by
  have := one_le_L s
  refine log_le_of_le_exp hy (by positivity) ?_
  rw [Real.exp_nat_mul]; exact h

end GlobalTheory.ColNorms.NumMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPerm
section
open scoped Classical

namespace GlobalTheory.JSW

theorem esymm_eq_sum_filter_perm (n j : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.esymm (Fin n) ℤ j =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        ∏ k ∈ J, (MvPolynomial.X (σ k) : MvPolynomial (Fin n) ℤ) := by
  rw [← MvPolynomial.rename_esymm (Fin n) ℤ j σ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.rename_X,
    Finset.powersetCard_eq_filter, Finset.powerset_univ]

theorem esymm_mul_alternant (n : ℕ) (m : Fin n → ℕ) (j : ℕ) :
    MvPolynomial.esymm (Fin n) ℤ j *
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [esymm_eq_sum_filter_perm n j σ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_mem, Finset.univ_inter]
  ring

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenProductSectionsIso
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAffineOpen_inf_preimage_of_isPullback {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y}
    {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY) [IsAffine S] {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) := by
  have : IsAffine _ := isAffineOpen_top S
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top
    rfl).isoPullback.hom

theorem appLE_appLE_of_comp {T X Y : Scheme.{0}} (f : T ⟶ X) (g : X ⟶ Y) (h : T ⟶ Y)
    (e : f ≫ g = h) {W : Y.Opens} {U : X.Opens} {N : T.Opens} (h1 : U ≤ g ⁻¹ᵁ W)
    (h2 : N ≤ f ⁻¹ᵁ U) (h3 : N ≤ h ⁻¹ᵁ W) (x : Γ(Y, W)) :
    (f.appLE U N h2).hom ((g.appLE W U h1).hom x) = (h.appLE W N h3).hom x := by
  subst e
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem functions_on_product_of_affine_opens : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (U : X.left.affineOpens) (V : Y.left.affineOpens), ∃ (W : (X ⊗ Y).left.affineOpens) (h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1) (h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1) (i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1) (i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1), W.1 = (fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1 ∧ (∀ b, i₁ b = ((fst X Y).left.appLE U.1 W.1 h₁).hom b) ∧ (∀ b, i₂ b = ((snd X Y).left.appLE V.1 W.1 h₂).hom b) ∧ Function.Bijective (Algebra.TensorProduct.productMap i₁ i₂) := by
  intro R _ X Y U V
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := .of_hasPullback _ _
  let W : (X ⊗ Y).left.affineOpens :=
    ⟨(fst X Y).left ⁻¹ᵁ U.1 ⊓ (snd X Y).left ⁻¹ᵁ V.1,
      isAffineOpen_inf_preimage_of_isPullback H U.2 V.2⟩
  have h₁ : W.1 ≤ (fst X Y).left ⁻¹ᵁ U.1 := inf_le_left
  have h₂ : W.1 ≤ (snd X Y).left ⁻¹ᵁ V.1 := inf_le_right
  let i₁ : Sec X.hom U.1 →ₐ[R] Sec (X ⊗ Y).hom W.1 :=
    { ((fst X Y).left.appLE U.1 W.1 h₁).hom with
      commutes' := fun r => by
        change ((fst X Y).left.appLE U.1 W.1 h₁).hom ((X.hom.appLE ⊤ U.1 le_top).hom _) =
          ((X ⊗ Y).hom.appLE ⊤ W.1 le_top).hom _
        exact appLE_appLE_of_comp _ _ _ (Over.w _) _ _ _ _ }
  let i₂ : Sec Y.hom V.1 →ₐ[R] Sec (X ⊗ Y).hom W.1 :=
    { ((snd X Y).left.appLE V.1 W.1 h₂).hom with
      commutes' := fun r => by
        change ((snd X Y).left.appLE V.1 W.1 h₂).hom ((Y.hom.appLE ⊤ V.1 le_top).hom _) =
          ((X ⊗ Y).hom.appLE ⊤ W.1 le_top).hom _
        exact appLE_appLE_of_comp _ _ _ (Over.w _) _ _ _ _ }
  refine ⟨W, h₁, h₂, i₁, i₂, rfl, fun b => rfl, fun b => rfl, ?_⟩
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V.1) (UX := U.1) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) V.2 U.2)

  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec X.hom U.1)))
      (CommRingCat.ofHom (algebraMap R (Sec Y.hom V.1)))
      ((fst X Y).left.appLE U.1 W.1 h₁) ((snd X Y).left.appLE V.1 W.1 h₂) := by
    refine po.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl (CommRingCat.of (Sec X.hom U.1)))
      (Iso.refl (CommRingCat.of (Sec Y.hom V.1)))
      (Iso.refl (CommRingCat.of (Sec (X ⊗ Y).hom W.1))) ?_ ?_ (by rfl) (by rfl)
    · ext r
      change (X.hom.appLE ⊤ U.1 le_top).hom r = (X.hom.appLE ⊤ U.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      congr 1
      simp
    · ext r
      change (Y.hom.appLE ⊤ V.1 le_top).hom r = (Y.hom.appLE ⊤ V.1 le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      congr 1
      simp
  have h1 := CommRingCat.isPushout_tensorProduct R (Sec X.hom U.1) (Sec Y.hom V.1)
  let e := h1.isoIsPushout _ _ po'
  have he : e.hom = CommRingCat.ofHom (Algebra.TensorProduct.productMap i₁ i₂).toRingHom := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po').trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_left_apply i₁ i₂ x).symm
    · refine (h1.inr_isoIsPushout_hom _ _ po').trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_right_apply i₁ i₂ x).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [he] at hb
  exact hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCbData
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.DefRowsCB

theorem exists_cbData : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (m : ℕ) (c : Fin (m + 1) → ℕ) (Xc : ∀ i, InfinitePlace K → Matrix (Fin (c i)) (Fin (c i)) ℂ) (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K) (t : Fin m → InfinitePlace K → ℝ), (∀ i v, IsUnit (Xc i v).det) → (∀ j v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v ((Kj j).mulVec x) ^ 2 ≤ Real.exp (t j v) * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc) v x ^ 2) → ∃ cb : CBData Xc Kj, ∀ j v, Real.log (cb.sq j v) ≤ t j v := by
  intro K _ _ _ _ m c Xc Kj t hX h
  refine ⟨{
    AA := fun _ => Unit
    Cl := fun _ _ => Unit
    W := fun i _ => EuclideanSpace ℂ (Fin (c i))
    γ := fun _ _ => 1
    Φ := fun i v x _ => WithLp.toLp 2 ((Xc i v)⁻¹.mulVec x)
    ε := fun _ _ _ _ => 1
    T := fun j v _ _ => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      ((Xc j.succ v)⁻¹ * (Kj j).map v.embedding * Xc j.castSucc v))
    hcl := fun _ => 1
    tmax := fun j v => Real.exp (t j v)
    hyp := ⟨hX, fun _ _ => ⟨one_pos, le_rfl⟩, ?_, ?_, fun _ _ _ _ => norm_one, ?_,
      fun _ _ => (Real.exp_pos _).le, fun _ _ => by simp⟩ }, ?_⟩
  · intro i v x
    rw [Formalism.DivisionValues.fnorm, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    simp
  · intro j v x
    funext q
    simp only [Formalism.DimensionVariation.liftOp, Fintype.sum_sigma, Finset.univ_unique, Finset.sum_singleton, Complex.ofReal_one,
      mul_one, one_smul, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX _ v), Matrix.mul_one]
  · intro j v _ _
    have key := Formalism.BasicNotions.opNormAt_sq_le (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) (hX _) v (IsTotallyComplex.isComplex v)
      (Matrix.mulVecLin (Kj j)) (Real.exp (t j v)) (Real.exp_pos _).le (fun x => by
        rw [← Formalism.BasicNotions.normAt_sq_eq_majAt, ← Formalism.BasicNotions.normAt_sq_eq_majAt]
        exact h j v x)
    have hm : LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
        (Matrix.mulVecLin (Kj j)) = Kj j := by
      ext a b
      simp [LinearMap.toMatrix_apply]
    have e : Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
        (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((Xc j.succ v)⁻¹ *
          (LinearMap.toMatrix (Pi.basisFun K (Fin (c j.castSucc))) (Pi.basisFun K (Fin (c j.succ)))
            (Matrix.mulVecLin (Kj j))).map v.embedding * Xc j.castSucc v))‖ := rfl
    rw [e, hm] at key
    exact key
  · intro j v
    show Real.log (Formalism.DimensionVariation.cbSq (Fintype.card Unit) (Fintype.card Unit) 1 1 (Real.exp (t j v))) ≤ t j v
    simp [Formalism.DimensionVariation.cbSq]

end GlobalTheory.DefRowsCB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.CurveTransport

open GlobalTheory.EllipticCM GlobalTheory.ConjPoint _root_.WeierstrassCurve
open GlobalTheory.Idele
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsLatOf IsInvIdealOf)

variable {K : Type} [Field K] [NumberField K]

theorem isLatOf_iff {ι : K →+* ℂ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair} :
    IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ Λ.lattice ↔ ∃ x ∈ 𝔞, ι x = z := by
  rw [IsLatOf, Set.ext_iff]
  rfl

theorem isInvIdealOf_inv_smul_one (t : (Af K)ˣ) :
    IsInvIdealOf t (t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K)) := by
  intro x
  rw [← algebraMap_mem_adelicIdeal (GlobalTheory.Idele.smul_ne_zero _ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)), ← mem_adelicIdeal_one_iff,
    ← mul_mem_adelicIdeal_smul t⁻¹ 1 ((t : Af K) * algebraMap K _ x), Units.inv_mul_cancel_left]

theorem mulEquiv_inv_mk (t : (Af K)ˣ) {x x' : K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) :
    mulEquiv t⁻¹ (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) rfl
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x' := by
  rw [mulEquiv_mk_eq_mk_iff_adelic]
  have e : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) x - algebraMap K (Af K) x' =
      ((t⁻¹ : (Af K)ˣ) : Af K) * -((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) := by
    rw [mul_neg, mul_sub, Units.inv_mul_cancel_left]
    ring
  rw [e, mul_mem_adelicIdeal_smul]
  exact neg_mem (mem_adelicIdeal_one_iff.2 h)

theorem exists_curve_torsTransport : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K],
    Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ →
    Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra;
    ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic)
      (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point),
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ),
        GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ →
        ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  intro K _ _ _ _ ι Λ₀ Ω₀ hΛ₀ hΩ₀
  letI : Algebra K ℂ := ι.toAlgebra
  have hAlg : ∀ y : K, algebraMap K ℂ y = ι y := fun _ => rfl
  have hsubIff : ∀ {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {Λ : PeriodPair},
      (IsLatOf ι 𝔞 Λ ↔ ∀ z, z ∈ idealSub 𝔞 ↔ z ∈ Λ.lattice) := fun {𝔞 Λ} => by
    rw [isLatOf_iff]
    exact forall_congr' fun z => by rw [mem_idealSub]; exact Iff.comm
  let M := GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀
  have hM : GlobalTheory.IsHomothetic Ω₀ Λ₀ M := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have hsub : ∀ z, z ∈ idealSub (1 : FractionalIdeal (𝓞 K)⁰ K) ↔ Ω₀ * z ∈ M.lattice := fun z => by
    rw [hM z]; exact hsubIff.1 hΛ₀ z
  obtain ⟨ξ, hξ, hξz⟩ := exists_isAnalyticIso (X := latticeCurve M) (C := 1) (one_smul _ _) hΩ₀ hsub
  refine ⟨latticeCurve M, inferInstance, ξ, hξ, fun σ t ht => ?_⟩
  obtain ⟨η, ⟨hη, hηx⟩, -⟩ := ht
  obtain ⟨L', g2, g3⟩ := GlobalTheory.CMRam.exists_conj_lattice σ.toRingEquiv M
  have h' : (1 : VariableChange ℂ) • (latticeCurve M).map (σ : ℂ →+* ℂ) = latticeCurve L' := by
    rw [one_smul]
    simp [latticeCurve, WeierstrassCurve.map, g2, g3, map_ofNat]
  obtain ⟨α, hα0, hα, hηα⟩ := hη.exists_mul h'
  let Λ₁ := GlobalTheory.scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁ : GlobalTheory.IsHomothetic α⁻¹ L' Λ₁ := GlobalTheory.isHomothetic_scalePeriods L' α⁻¹ (inv_ne_zero hα0)
  have hΛ₁' : GlobalTheory.IsHomothetic α Λ₁ L' := fun z => by
    rw [← hΛ₁ (α * z), ← mul_assoc, inv_mul_cancel₀ hα0, one_mul]
  have hlat1 : IsLatOf ι (t⁻¹ • 1) Λ₁ := hsubIff.2 fun z => by rw [hα, hΛ₁' z]
  refine ⟨Λ₁, α, hΩ₀, hα0, fun x => σ.commutes x, hΛ₀, ⟨_, isInvIdealOf_inv_smul_one t, hlat1⟩, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, ← hM.g₂_eq, ← g2, hΛ₁'.g₂_eq, div_eq_inv_mul]
  · rw [div_eq_inv_mul, ← hM.g₃_eq, ← g3, hΛ₁'.g₃_eq, div_eq_inv_mul]
  · intro x x' hx hint
    have e := hηx (Submodule.Quotient.mk x)
    rw [mulEquiv_inv_mk t hint, torsionIncl_mk, torsionIncl_mk, hξz, hηα, hAlg, hAlg] at e
    have hxM : Ω₀ * ι x ∉ M.lattice := fun h => hx ((hM _).1 h)
    rw [latticePoint_of_notMem M hxM] at e
    have hx' : α * ι x' ∉ L'.lattice := by
      intro h
      rw [latticePoint_of_mem L' h, map_zero, variableChangePoint_some] at e
      exact Affine.Point.some_ne_zero _ e
    rw [latticePoint_of_notMem L' hx', variableChangePoint_some, variableChangePoint_some] at e
    change Affine.Point.some _ _ _ = _ at e
    rw [Affine.Point.some.injEq] at e
    simp [VariableChange.one_def] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rw [div_eq_inv_mul, ← hM.weierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.weierstrassP_mul]
      exact e1
    · rw [div_eq_inv_mul, ← hM.derivWeierstrassP_mul, div_eq_inv_mul, ← hΛ₁'.derivWeierstrassP_mul]
      rw [map_ofNat σ 2, div_left_inj' two_ne_zero] at e2
      exact e2

end GlobalTheory.LatVal.CurveTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNe
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GramVec

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
  {J : Matrix (Fin M) (Fin M) E}

theorem hE_add_smul_right (z u v : Fin M → E) (c : E) :
    hE σ J z (u + c • v) = hE σ J z u + c * hE σ J z v := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_left (z u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) z = hE σ J u z + σ c * hE σ J v z := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_self (u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) (u + c • v) =
      hE σ J u u + c * hE σ J u v + σ c * hE σ J v u + σ c * c * hE σ J v v := by
  rw [hE, GlobalTheory.HermLineZeros.hform_expand]
  rfl

theorem hE_single (i j : Fin M) : hE σ J (Pi.single i 1) (Pi.single j 1) = J i j :=
  GlobalTheory.HermLineZeros.hform_single _ J i j

theorem hermitianGramDetTwoVectors_comm (x z : Fin M → E) : gram2E σ J x z = gram2E σ J z x := by
  unfold gram2E; ring

noncomputable def gramPoly (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (z a b : Fin M → E) : Polynomial E :=
  Polynomial.C (hE σ J z z) * (Polynomial.C (hE σ J a a) + Polynomial.X * Polynomial.C (hE σ J a b + hE σ J b a)
      + Polynomial.X ^ 2 * Polynomial.C (hE σ J b b))
    - (Polynomial.C (hE σ J z a) + Polynomial.X * Polynomial.C (hE σ J z b))
      * (Polynomial.C (hE σ J a z) + Polynomial.X * Polynomial.C (hE σ J b z))

theorem hermitianGramDetTwoVectors_eval_line (z a b : Fin M → E) (t : E) (ht : σ t = t) :
    gram2E σ J z (a + t • b) = (gramPoly σ J z a b).eval t := by
  unfold gram2E gramPoly
  rw [hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, ht]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem exists_gram2E_ne (h : IsCMExt F E σ) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    (z : Fin M → E) (hz : hE σ J z z ≠ 0) : ∃ w, gram2E σ J z w ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set a : Fin M → E := fun i => hE σ J (Pi.single i 1) z
  set b : Fin M → E := fun j => hE σ J z (Pi.single j 1)
  have hdiag : ∀ i, hE σ J z z * J i i - b i * a i = 0 := fun i => by
    have := hc (Pi.single i 1)
    simpa [gram2E, hE_single] using this
  have key : hE σ J z z • J = Matrix.vecMulVec a b := by
    ext i j
    have e1 := hc (Pi.single i 1 + (1 : E) • Pi.single j 1)
    have e2 := hc (Pi.single i 1 + d • Pi.single j 1)
    simp only [gram2E, hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, hE_single,
      map_one] at e1 e2
    have e0i := hdiag i
    have e0j := hdiag j
    have : (d - σ d) * (hE σ J z z * J i j - a i * b j) = 0 := by
      simp only [a, b] at e0i e0j ⊢
      linear_combination e2 - e0i - σ d * d * e0j - σ d * (e1 - e0i - e0j)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hd
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      exact sub_eq_zero.1 h0
  have hdet : (hE σ J z z • J).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz) hJ.2
  have hunit : IsUnit (hE σ J z z • J) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hr := Matrix.rank_of_isUnit _ hunit
  have hle : (Matrix.vecMulVec a b).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq Unit]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  rw [key, Fintype.card_fin] at hr
  omega

end CM

end GlobalTheory.GramVec

open GlobalTheory.GramVec in
theorem GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  intro F E _ _ _ _ _ σ h M J hM hJ x y hx hy
  obtain ⟨w0, h0⟩ := exists_gram2E_ne h hM hJ x hx
  obtain ⟨w1, h1⟩ := exists_gram2E_ne h hM hJ y hy
  set Px := gramPoly σ J x w0 (w1 - w0)
  set Py := gramPoly σ J y w0 (w1 - w0)
  have hPx : Px ≠ 0 := by
    intro h0'
    apply h0
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) x w0 (w1 - w0) 0 (map_zero σ)
    rw [zero_smul, add_zero] at this
    rw [this]; change Polynomial.eval 0 Px = 0; rw [h0', Polynomial.eval_zero]
  have hPy : Py ≠ 0 := by
    intro h1'
    apply h1
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) y w0 (w1 - w0) 1 (map_one σ)
    rw [one_smul, add_sub_cancel] at this
    rw [this]; change Polynomial.eval 1 Py = 0; rw [h1', Polynomial.eval_zero]
  have hfin : {f : F | Px.IsRoot (algebraMap F E f) ∨ Py.IsRoot (algebraMap F E f)}.Finite := by
    have := ((Polynomial.finite_setOf_isRoot hPx).union (Polynomial.finite_setOf_isRoot hPy)).preimage
      (FaithfulSMul.algebraMap_injective F E).injOn
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨f, hf⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, Polynomial.IsRoot.def] at hf
  have hfix : σ (algebraMap F E f) = algebraMap F E f := σ.commutes f
  refine ⟨w0 + algebraMap F E f • (w1 - w0), ?_, ?_⟩
  · rw [hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.1
  · rw [hermitianGramDetTwoVectors_comm, hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.2
end
end

