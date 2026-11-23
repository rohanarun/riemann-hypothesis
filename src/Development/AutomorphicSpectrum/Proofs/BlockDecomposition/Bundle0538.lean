module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0097
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  {Ω₀ Ω : Type*} [Field Ω₀] [Field Ω]

def scaleT (c : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k => C (c k) * X k

theorem scaleT_injective (c : K → Ω) (hc : ∀ k, c k ≠ 0) : Function.Injective (scaleT c) := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleT fun k => (c k)⁻¹) fun f => by
    simpa using congrArg (fun g => g f) h

theorem imageZ_mCoordIdeal_of_eq (κ : K → K') (hκ : Function.Injective κ) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (hv : ∀ p, (v p).1 = κ p.1) (φ : Ω₀ →+* Ω) (b : K → Ω) (hb : ∀ k, b k ≠ 0)
    (y₀ : (Σ k, ι k) → Ω₀) (y : (Σ k', ι' k') → Ω) (h : ∀ p, φ (y₀ p) = b p.1 * y (v p)) :
    imageZ v (Geo.mCoordIdeal y) = Geo.mCoordIdeal y₀ := by
  let ψ : MvPolynomial K Ω₀ →+* MvPolynomial K' Ω :=
    ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).toRingHom.comp
      (scaleT fun k => (b k)⁻¹).toRingHom).comp (MvPolynomial.map φ)
  have hψ : Function.Injective ψ :=
    (rename_injective κ hκ).comp ((scaleT_injective _ fun k => inv_ne_zero (hb k)).comp
      (map_injective φ φ.injective))
  have key : ∀ f : Geo.MRing ι, ψ (Geo.mConeMap y₀ f) = Geo.mConeMap y (rename v f) := by
    intro f
    have e : ψ.comp (Geo.mConeMap y₀ : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω₀).toRingHom =
        ((Geo.mConeMap y : Geo.MRing ι' →ₐ[ℤ] MvPolynomial K' Ω).toRingHom.comp
          (rename v : Geo.MRing ι →ₐ[ℤ] Geo.MRing ι').toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
      · simp
      · simp only [ψ, Geo.mConeMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
          rename_X, map_mul, map_C, map_X, scaleT, algHom_C, rename_C]
        rw [hv p, h p]
        simp only [MvPolynomial.algebraMap_eq, rename_C]
        rw [← mul_assoc, ← C_mul, mul_comm (b p.1), mul_assoc, mul_inv_cancel₀ (hb p.1), mul_one]
    exact congrArg (fun g => g f) e
  ext f
  simp only [imageZ, Geo.mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← key, map_eq_zero_iff ψ hψ]

end Alg

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem evaluation_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (resG X h s) = X.evaluation U x (h hx) s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem ptCoord_qpSnd (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (k : Fin (m + 1)) :
    ∃ b : (MP ℤ (m + 1) (consN n' n)).residueField x, b ≠ 0 ∧ ∀ i : Bk n k,
      (qpSnd n' m n).residueFieldMap x (ptCoord (qpSnd n' m n x) ⟨k, i⟩) = b * ptCoord x ⟨k.succ, i⟩ := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  let P : MP ℤ (m + 1) (consN n' n) ⟶ PSpace ℤ (n k) := prB (consN n' n) k.succ
  have hP : F ≫ prB n k = P := rfl
  let c₀ := ptChart (F x) k
  let c₁ := ptChart x k.succ
  have hx₀ : F x ∈ blockChart n k c₀ := mem_ptChart _ _
  have hx₁ : x ∈ blockChart (consN n' n) k.succ c₁ := mem_ptChart _ _
  let W₀ : (MP ℤ (m + 1) (consN n' n)).Opens := F ⁻¹ᵁ blockChart n k c₀
  let W₁ : (MP ℤ (m + 1) (consN n' n)).Opens := blockChart (consN n' n) k.succ c₁
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := le_rfl
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := inf_le_right.trans h₁
  have e₀ : ∀ i : Bk n k, F.residueFieldMap x (ptCoord (F x) ⟨k, i⟩) =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ i) := by
    intro i
    show F.residueFieldMap x ((MP ℤ m n).evaluation (blockChart n k c₀) (F x) hx₀
      (pullRatio (prB n k) _ c₀ le_rfl i)) = _
    rw [Scheme.evaluation_naturality_apply, Scheme.Hom.app_eq_appLE, appLE_pullRatio,
      ← evaluation_resG (inf_le_left : V ≤ W₀) x hxV, resG_pullRatio]
    rfl
  have e₁ : ∀ i : Bk n k, ptCoord x ⟨k.succ, i⟩ =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₁ hV₁ i) := by
    intro i
    show (MP ℤ (m + 1) (consN n' n)).evaluation W₁ x hx₁ (pullRatio P W₁ c₁ h₁ i) = _
    rw [← evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  refine ⟨(MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ c₁), ?_, fun i => ?_⟩
  · intro h0
    have e := congrArg ((MP ℤ (m + 1) (consN n' n)).evaluation V x hxV)
      ((pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := c₀)).trans pullRatio_self)
    rw [map_mul, h0, zero_mul, map_one] at e
    exact zero_ne_one e
  · refine (e₀ i).trans ?_
    rw [e₁ i, ← map_mul]
    exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := i)).symm

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem imageZ_ptIdeal (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) :
    imageZ (sv n' n) (ptIdeal x) = ptIdeal (qpSnd n' m n x) := by
  choose b hb h using ptCoord_qpSnd n' m n x
  exact imageZ_mCoordIdeal_of_eq Fin.succ (Fin.succ_injective _) (sv n' n) (fun _ => rfl)
    ((qpSnd n' m n).residueFieldMap x).hom b hb (ptCoord (qpSnd n' m n x)) (ptCoord x) fun p => h p.1 p.2

end GlobalTheory.CompanionTheory.MPDict.ProjImage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  have hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s := fun w ↦ by
    have hr : w.IsReal := IsTotallyReal.isReal w
    have hp := infiniteParams_eq_zero χ hχ w
    simp [HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau,
      HeckeCharacter.infiniteWeight, hp]
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  rw [HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const,
    Finset.card_univ, hcard]

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem hasInfChar_conj_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) (hB : IsHerm π B) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : π.HasInfChar τ m) (hm' : π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨φ, hφ⟩ := hB.2
  refine _root_.GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq a m m' hm.1 hm'.1 fun u => ?_
  have val : ∀ (σ : E →+* ℂ) (l : Multiset ℂ), π.HasInfChar σ l → ∀ w : ℂ,
      Formalism.REAL.qdet (EopV π σ) (w + ((a : ℂ) - 1) / 2) φ = (l.map (w + ·)).prod • φ := by
    intro σ l hl w
    apply Subtype.ext
    rw [_root_.GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val E a π σ w φ, hl.2 w φ.1 φ.2]
    rfl
  have key := GlobalTheory.T.quantum_det_adjoint_form π.V B a (EopV π τ) (EopV π (NumberField.ComplexEmbedding.conjugate τ))
    (_root_.GlobalTheory.CompanionTheory.Clozel.glRel_EopV E a π _) (_root_.GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint E a π B hB τ) (u + ((a : ℂ) - 1) / 2) φ φ
  have arg : (a : ℂ) - 1 - (starRingEnd ℂ) (u + ((a : ℂ) - 1) / 2) =
      -(starRingEnd ℂ) u + ((a : ℂ) - 1) / 2 := by
    simp only [map_add (f := _), map_div₀, map_sub, map_one, Complex.conj_natCast, map_ofNat]
    ring
  rw [arg, val τ m hm u, LinearMap.smul_apply, val _ m' hm' (-(starRingEnd ℂ) u)] at key
  simp only [map_smul, LinearMap.smul_apply, smul_smul, map_smulₛₗ, smul_eq_mul] at key
  exact mul_right_cancel₀ hφ key

end GlobalTheory.CompanionTheory.Clozel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmooth
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem pairing_phi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ hψ h1 n s V V' _ _ _ _ T T' hT hT' B hB hnd
  borelize k
  let ν : Measure k := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hinv : TwInv T T' B s := hB
  have hlin := _root_.GlobalTheory.CompanionTheory.MirPair.EvLin.evVal_additive_homogeneous ν ψ T B hψ hT
  have hex := _root_.GlobalTheory.CompanionTheory.MirPair.exists_evVal ν ψ c T T' B s hψ hc hT hT' hinv
  have huniq : ∀ {v v' A A'}, EvVal ν ψ T B v v' A → EvVal ν ψ T B v v' A' → A = A' := by
    rintro v v' A A' ⟨t₀, h₀⟩ ⟨t₁, h₁⟩
    rcases le_total (valuation k (t₀ : k)) (valuation k (t₁ : k)) with h | h
    · rw [← h₀ t₁ h, h₁ t₁ le_rfl]
    · rw [← h₀ t₀ le_rfl, h₁ t₀ h]
  choose f hf using hex
  let B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ f
    (fun v₁ v₂ v' => huniq (hf _ _) (hlin.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.1 _ _ _ _ (hf _ _)))
    (fun v v₁ v₂ => huniq (hf _ _) (hlin.2.2.1 _ _ _ _ _ (hf _ _) (hf _ _)))
    (fun z v v' => huniq (hf _ _) (hlin.2.2.2 _ _ _ _ (hf _ _)))
  have hB₀ : ∀ v v', B₀ v v' = f v v' := fun _ _ => rfl
  refine _root_.GlobalTheory.CompanionTheory.MirPair.Descend.descend ψ n s V V' T T' B₀ ?_ ?_ ?_ ?_
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (_root_.GlobalTheory.CompanionTheory.MirPair.EvVal_translate ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).1
  · intro y v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (_root_.GlobalTheory.CompanionTheory.MirPair.EvVal_translate ν ψ T T' B s hψ hT hinv y v v' _ (hf _ _)).2
  · intro p v v'
    rw [hB₀, hB₀]
    exact huniq (hf _ _) (_root_.GlobalTheory.CompanionTheory.MirPair.evVal_conj ν ψ c T T' B s hψ hc hT hT' hinv p v v' _ (hf _ _))
  · intro v hv
    obtain ⟨v', A, hA, hA0⟩ := _root_.GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero ν ψ c T T' B s hψ hc hT hT' hinv hnd v hv
    exact ⟨v', by rw [hB₀, huniq (hf _ _) hA]; exact hA0⟩

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def scalT {K : Type} [Mul K] {n M : ℕ} (c : K) (y : Fin n → Fin M → K) : Fin n → Fin M → K :=
  fun p i => c * y p i

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F}

def qv (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)


variable (E) in
def zetaV (v : HeightOneSpectrum (𝓞 F)) (s : ℕ) : ℝ :=
  open Classical in
  if IsField (Fv F v ⊗[F] E) then (1 - ((qv v : ℝ) ^ (2 * s))⁻¹)⁻¹ else ((1 - ((qv v : ℝ) ^ s)⁻¹)⁻¹) ^ 2

def IsContent (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type}
    (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ) : Prop :=
  (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧
  (∀ i (lam : Measure (Fv F v)), IsStdV v lam →
    (coordK (Fv F v) b lam).map (fun x => c i * x) = (qv v ^ w i) • coordK (Fv F v) b lam) ∧
  (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧
    ‖t‖ = ((qv v : ℝ) ^ w i)⁻¹) ∧
  (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧
  (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j)

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFreeFramePairs
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FreeFrames

theorem isOpen_free_frame_pairs {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (r t a : ℕ) (e : R) (he : e * e = e) (U : Set R) (hU : IsOpen U) (h1 : (1 : R) ∈ U)
    (hb : ∀ x ∈ U, ∃ b, x * b = e) :
    IsOpen {z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R |
      ∃ (L₁ : Matrix (Fin r) (Fin a) R) (L₂ : Matrix (Fin t) (Fin a) R),
        L₁ * (e • z.1) = e • 1 ∧ L₁ * (e • z.2) = 0 ∧ L₂ * (e • z.1) = 0 ∧ L₂ * (e • z.2) = e • 1} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro z₀ ⟨L₁, L₂, h11, h12, h21, h22⟩
  let L : Matrix (Fin r ⊕ Fin t) (Fin a) R := Matrix.fromRows L₁ L₂
  let Z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin a) (Fin r ⊕ Fin t) R :=
    fun z => Matrix.fromCols (e • z.1) (e • z.2)
  let C : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R :=
    fun z => L * Z z + (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R)
  have hone : (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) = Matrix.fromBlocks 1 0 0 1 :=
    Matrix.fromBlocks_one.symm
  have hLZ : L * Z z₀ = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [L, Z]
    rw [Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  have hC0 : C z₀ = 1 := by
    simp only [C]
    rw [hLZ, ← add_smul]
    simp
  have hZc : Continuous Z := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.1 i j :=
        Continuous.mul continuous_const (continuous_fst.matrix_elem i j)
      simpa [Z] using h
    | inr j =>
      have h : Continuous fun z : Matrix (Fin a) (Fin r) R × Matrix (Fin a) (Fin t) R => e * z.2 i j :=
        Continuous.mul continuous_const (continuous_snd.matrix_elem i j)
      simpa [Z] using h
  have hCc : Continuous C := by
    exact (continuous_const.matrix_mul hZc).add continuous_const
  have hd : Continuous fun z => (C z).det := hCc.matrix_det
  have hnhds : (fun z => (C z).det) ⁻¹' U ∈ 𝓝 z₀ := by
    refine (hU.preimage hd).mem_nhds ?_
    simpa [Set.mem_preimage, hC0] using h1
  refine Filter.mem_of_superset hnhds ?_
  intro z hz
  obtain ⟨b, hb'⟩ := hb _ hz
  have hLz : L * Z z = C z - (1 - e) • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    simp only [C, add_sub_cancel_right]
  have hee : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have key : ((e * b) • ((C z).adjugate * L)) * Z z = e • (1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc, hLz, Matrix.mul_sub, Matrix.adjugate_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_sub, smul_smul, smul_smul]
    have h2 : e * b * (1 - e) = 0 := by
      rw [mul_right_comm, hee, zero_mul]
    have h3 : e * b * (C z).det = e := by
      rw [mul_assoc, mul_comm b, hb', he]
    rw [h2, h3, zero_smul, sub_zero]
  set L' := (e * b) • ((C z).adjugate * L) with hL'
  have key' : Matrix.fromBlocks (L'.toRows₁ * (e • z.1)) (L'.toRows₁ * (e • z.2))
      (L'.toRows₂ * (e • z.1)) (L'.toRows₂ * (e • z.2)) =
      Matrix.fromBlocks (e • 1) 0 0 (e • 1) := by
    rw [← Matrix.fromRows_mul_fromCols, Matrix.fromRows_toRows]
    have := key
    simp only [Z] at this
    rw [this, hone, Matrix.fromBlocks_smul]
    simp only [smul_zero]
  obtain ⟨a1, a2, a3, a4⟩ := Matrix.fromBlocks_inj.1 key'
  exact ⟨L'.toRows₁, L'.toRows₂, a1, a2, a3, a4⟩

theorem isOpen_free : ∀ (D : D7) (r t a : ℕ) (e : AE D), e * e = e →
    (∃ U : Set (AE D), IsOpen U ∧ 1 ∈ U ∧ ∀ x ∈ U, ∃ b, x * b = e) →
    IsOpen {z : Mx D a r × Mx D a t | Free e (e • z.1, e • z.2)} := by
  rintro D r t a e he ⟨U, hU, h1, hb⟩
  exact isOpen_free_frame_pairs r t a e he U hU h1 hb

end GlobalTheory.CompanionTheory.FreeFrames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.TotalTrace

theorem eq_zero_of_exp_mul_eq_one {c : ℂ} (h : ∀ t : ℝ, Complex.exp (c * t) = 1) : c = 0 := by
  have h0 : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h1 := h0.cexp
  have h2 : (fun t : ℝ => Complex.exp (c * t)) = fun _ => 1 := funext h
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using h3

theorem total_trace_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {m : (E →+* ℂ) → Multiset ℂ} (hV : IsDiscrete V)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hφ0 (Subtype.ext (funext hcon))
  have hlie : lie E N (oneL E N) φ = (∑ τ, (m τ).sum) • φ := by
    rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.CompanionTheory.CentEig.trace_Eop_eq_of_hasInfCharGL (hm τ) φ hφ
  refine eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ hlie t g
  rw [(hV.sqInt φ hφ).1 t g] at h1
  have h2 : Complex.exp ((∑ τ, (m τ).sum) * t) * φ.1 g = 1 * φ.1 g := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hg h2

theorem twBound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  intro E _ _ _ N
  refine ⟨0, fun V m hV hm => ?_⟩
  rw [total_trace_eq_zero hV hm, norm_zero]

end GlobalTheory.CompanionTheory.TotalTrace

end
end

