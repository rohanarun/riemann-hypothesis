module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtMixedModelSourceDualLineLinearForm
section
namespace I195MixedCoordinates_9421736abf21ec81fbe38545

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_9421736abf21ec81fbe38545

public noncomputable abbrev _root_.I195MixedCoordinates_535b308549effaf3d84d5b0a.source :=
  @_root_.I195MixedCoordinates_9421736abf21ec81fbe38545.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf

theorem hasDerivAt_mixS_extY : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ Mx D T.rank ρ, Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ x w, HasDerivAt (fun t : ℝ => ψ (symplO S T (d.extX T x) (d.extY T (L t))) * (_root_.I195MixedCoordinates_9421736abf21ec81fbe38545.source d) T ψ v.μ v.𝓕 f x w) ((_root_.I195MixedCoordinates_9421736abf21ec81fbe38545.source d) T ψ v.μ v.𝓕 (fun p => deriv (fun t : ℝ => heisO ψ S T (d.extY T (L t)) f p) 0) x w) 0 := by
  intro D ψ hψ θ hθ S S₀ T ρ d v f hf L hLc hLf x w
  let M : ℝ →+ WO S T := (d.extY T).comp L
  have hM : Formalism.L2.Theta.IsRealDir T S M := by
    have hc : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
    refine ⟨hc.comp hLc, fun t => ?_⟩
    show (d.extY T (L t)).map (finPart D) = 0
    rw [HypDec.extY_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, v.covol.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hM hf)
  have e1 : (fun t : ℝ => ψ (symplO S T (d.extX T x) (d.extY T (L t))) * (_root_.I195MixedCoordinates_9421736abf21ec81fbe38545.source d) T ψ v.μ v.𝓕 f x w) =
      fun t => (_root_.I195MixedCoordinates_9421736abf21ec81fbe38545.source d) T ψ v.μ v.𝓕 (heisO ψ S T (M t) f) x w := by
    funext t
    have h := congrFun ((_root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf).2.1 x (L t)) w
    rw [Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have e2 : (fun p => deriv (fun t : ℝ => heisO ψ S T (d.extY T (L t)) f p) 0) =
      heisO ψ S T (M 0) (GlobalTheory.OrientedHeis.dLine ψ S T M f) := by
    rw [M.map_zero, GlobalTheory.OrientedHeis.heisO_zero]
    rfl
  rw [e1, e2]
  have hI : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IntegrableOn (fun a => ψ (symplOH S T (d.extY T a) (d.extX T x)) *
      g (d.extY T a + d.extX T x + d.ext0 T w)) v.𝓕 v.μ := fun g hg => by
    simpa only [HypDec.integrandS_eq] using HypDec.integrableOn_mixS d hψ.1.1 v.covol hg x w
  change HasDerivAt (fun t : ℝ => ∫ a in v.𝓕,
    heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x)
      (heisO ψ S T (d.ext0 T w) (heisO ψ S T (M t) f))) 0 ∂v.μ)
    (∫ a in v.𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x)
      (heisO ψ S T (d.ext0 T w)
        (heisO ψ S T (M 0) (GlobalTheory.OrientedHeis.dLine ψ S T M f)))) 0 ∂v.μ) 0
  simp only [HypDec.integrandS_eq]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := v.μ.restrict v.𝓕) (x₀ := (0 : ℝ))
    (F' := fun t a => ψ (symplOH S T (d.extY T a) (d.extX T x)) *
      heisO ψ S T (M t) (GlobalTheory.OrientedHeis.dLine ψ S T M f) (d.extY T a + d.extX T x + d.ext0 T w))
    (bound := fun _ => K) (s := Set.univ) Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const K) ?_).2
  · exact Filter.Eventually.of_forall fun t =>
      (hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 t) hf)).aestronglyMeasurable
  · exact hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 0) hf)
  · exact (hI _ (GlobalTheory.OrientedHeis.theta_heisO_real hθ hψ (hM.2 0)
      (GlobalTheory.OrientedHeis.theta_dLine hθ hψ hM hf))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a t _ => ?_
    rw [norm_mul, hψ.1.2.1, one_mul]
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hK _
  · exact Filter.Eventually.of_forall fun a t _ =>
      (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hM hf _ t).const_mul _

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
section
noncomputable section

namespace GlobalTheory.Core.Rk.IwSplit

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
open Formalism.UG (bc stabGL GLint cT)

section Pure

variable {A : Type} [CommRing A] {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq m] [DecidableEq ι] (e : m ⊕ m ≃ ι)

def shear : GL ι A :=
  ⟨(Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 0 (-1) 1).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp,
    by rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]; simp⟩

theorem shear_mulVec (x y : m → A) : (shear e).1 *ᵥ pairVec e x y = pairVec e x (x + y) := by
  simp [mulVec_pairVec, shear]

theorem bc_shear {B : Type} [CommRing B] (f : A →+* B) : bc f (shear e) = shear e :=
  Units.ext (by
    change ((Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm).map f =
      (Matrix.fromBlocks 1 0 1 1).submatrix e.symm e.symm
    simp [← Matrix.submatrix_map, Matrix.fromBlocks_map])

omit [DecidableEq m] [DecidableEq ι] in
theorem pair_dblGram (J : Matrix m m A) (x y x' y' : m → A) :
    pairVec e x y ⬝ᵥ dblGram e J *ᵥ pairVec e x' y' = x ⬝ᵥ J *ᵥ x' - y ⬝ᵥ J *ᵥ y' := by
  rw [dblGram, blkMat_mulVec, Matrix.neg_mulVec]
  simp [dotProduct, ← e.sum_comp, sub_eq_add_neg]

theorem keepsDiag_of_pairing {J : Matrix m m A} (hJ : IsUnit J.det) {x : Matrix ι ι A} {y : GL ι A}
    (h : ∀ u' u, (x *ᵥ u') ⬝ᵥ dblGram e J *ᵥ (y.1 *ᵥ u) = u' ⬝ᵥ dblGram e J *ᵥ u) (hy : y ∈ stabGL (diagSub A e)) :
    KeepsDiag e x := by
  refine keepsDiag_of_mulVec fun w hw => ?_
  obtain ⟨a, rfl⟩ := (mem_diagSub e).1 hw
  obtain ⟨s, t, hst⟩ : ∃ s t, x *ᵥ pairVec e a a = pairVec e s t := ⟨_, _, (pairVec_eta e _).symm⟩
  rw [hst, pairVec_mem_diagSub, ← sub_eq_zero]
  have h1 : ∀ b, (s - t) ⬝ᵥ J *ᵥ b = 0 := fun b => by
    obtain ⟨c, hc⟩ := (mem_diagSub e).1 ((inv_mem hy (pairVec e b b)).1 ((pairVec_mem_diagSub e).2 rfl))
    have h2 := h (pairVec e a a) ((y⁻¹).1 *ᵥ pairVec e b b)
    rw [Matrix.mulVec_mulVec _ y.1, Units.mul_inv, Matrix.one_mulVec, hst, hc, pair_dblGram, pair_dblGram,
      sub_self] at h2
    rw [sub_dotProduct, h2]
  funext i
  have h3 := h1 (J⁻¹ *ᵥ Pi.single i 1)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mulVec, dotProduct_single, mul_one] at h3

end Pure

theorem iwasawa_diag {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {n : ℕ} (x : GL (Fin (n + n)) K) : ∃ k : GL (Fin (n + n)) V,
    x * bc (algebraMap V K) k ∈ stabGL (diagSub K (finSumFinEquiv (m := n) (n := n))) := by
  obtain ⟨k, b, hb, h⟩ := GlobalTheory.ValIwasawa.iwasawa V K (n + n) (x⁻¹ * shear finSumFinEquiv)
  refine ⟨k * (shear finSumFinEquiv)⁻¹, inv_mem_iff.1 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_))⟩
  obtain ⟨a, rfl⟩ := (mem_diagSub _).1 hw
  have h1 : (x * bc (algebraMap V K) (k * (shear finSumFinEquiv)⁻¹))⁻¹ * shear finSumFinEquiv =
      shear finSumFinEquiv * b := by
    rw [map_mul, map_inv, bc_shear, mul_inv_rev, mul_assoc, h, mul_inv_rev, inv_inv, mul_assoc]
    exact congrArg _ (inv_mul_cancel_left _ _)
  have h2 : (b.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
    ext i j
    refine hb ?_
    change (Fin.castAdd n j : ℕ) < Fin.natAdd n i
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h3 : pairVec finSumFinEquiv a a = (shear finSumFinEquiv).1 *ᵥ pairVec finSumFinEquiv a 0 := by
    rw [shear_mulVec, add_zero]
  rw [h3, Matrix.mulVec_mulVec, ← Units.val_mul, h1, Units.val_mul, ← Matrix.mulVec_mulVec,
    mulVec_pairVec _ b.1, h2, shear_mulVec, pairVec_mem_diagSub]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_siegelH_of_split (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : J.det ≠ 0)
    (τ : E →ₐ[F] Fv F v) {g : GLoc σ Q v} (hg : splitHom σ Q τ g ∈ stabGL (diagSub (Fv F v) finSumFinEquiv)) :
    g ∈ siegelH (Fv F v) σ Q := by
  have e : Q.map τ = dblGram finSumFinEquiv (J.map τ) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), dblGram, Matrix.map_neg _ (map_neg _)]
  have hu : IsUnit (J.map τ).det := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact ((map_ne_zero τ).2 hJ).isUnit
  have h1 := (keepsDiag_iff _).1 (mem_stabGL_diagSub.1 hg)
  have h2 := (keepsDiag_iff _).1 (keepsDiag_of_pairing finSumFinEquiv hu (x := (splitHom σ Q (τ.comp σ) g).1)
    (fun u' u => e ▸ pairing_splitHom τ g u' u) hg)
  refine mem_siegelOf.2 ((keepsDiag_iff _).2 fun i j => split_ext h τ ?_ ?_)
  · rw [map_add (f := _), map_add (f := _)]; exact h1 i j
  · rw [map_add (f := _), map_add (f := _)]; exact h2 i j

theorem hasIwasawa_of_algHom (h : IsCMExt F E σ) (hQ : Q = dblGram finSumFinEquiv J) (hJ : IsHermND σ J)
    (hQ' : IsHermND σ Q) (τ : E →ₐ[F] Fv F v) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (hL : IsSelfDualAt σ J L v) : HasIwasawa σ Q (KFin σ Q L v) := fun g => by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hβ := (isLatticeFrame_dbl ha).isSplitBasis τ h
  rw [bc_blkGL, bc_blkGL] at hβ
  generalize bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (bc (compFin F E v) a) = β at hβ
  have hd : blkGL finSumFinEquiv (β, β) ∈ stabGL (diagSub (Fv F v) finSumFinEquiv) :=
    mem_stabGL_diagSub.2 ((keepsDiag_blkMat _).2 rfl)
  obtain ⟨k, hk⟩ := iwasawa_diag (V := v.adicCompletionIntegers F) (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β)) g)
  obtain ⟨κ, hκ⟩ := (splitEquivIn h hQ' τ (blkGL finSumFinEquiv (β, β))).surjective
    (bc (algebraMap (v.adicCompletionIntegers F) (Fv F v)) k)
  have h1 : κ ∈ KFin σ Q L v :=
    (mem_stabLoc_iff_GLint h hQ' (isSelfDualAt_dbl hQ hL) hβ).2 (hκ ▸ ⟨k, rfl⟩)
  rw [← hκ, ← map_mul, splitEquivIn_apply] at hk
  have h2 := mul_mem (mul_mem hd hk) (inv_mem hd)
  rw [← mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right] at h2
  exact ⟨⟨g * κ, mem_siegelH_of_split h hQ hJ.2 τ h2⟩, κ⁻¹, inv_mem h1, (mul_inv_cancel_right g κ).symm⟩

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSelfDualAt_of_isSelfDualC {D : D7} {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) (v : FinPl D) :
    IsSelfDualAt D.sp.cm.sig A.gram L v :=
  (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL)).2
    (fun y => hL.2 y) v

theorem hasIwasawa_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D,
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v →
    HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  intro D A L hL v ⟨P, P', hne, hP, hP'⟩
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  exact hasIwasawa_of_algHom (isCMExt_host D) (gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
    (GlobalTheory.Doubling.isHermND_gram (dblSp A)) τ L (isSelfDualAt_of_isSelfDualC hL v)

end Record

end GlobalTheory.Core.Rk.IwSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HdNumbers
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk

noncomputable section

namespace GlobalTheory.Core.Rk

theorem hd_numbers : ∀ (D : D7) (u : D.what₂.Word) (L C' Cl Cg cb Cu cT CT : ℝ), HD D L C' Cl Cg cb Cu cT CT →
    5 ≤ mfL D L ∧ 4 * D.R.f + 1 ≤ (D.mem u).A.T ∧ 0 < d0 D u ∧ 5 ≤ (D.R.f : ℝ) * D.R.k * L := by
  intro D u L C' Cl Cg cb Cu cT CT h
  obtain ⟨-, -, hH, hN, -⟩ := h
  obtain ⟨hL1, -, hmf, hfk, -, -, -, -, -, -, -, hg0, -, hg1, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, hT, hdu, -⟩ := hN
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hm4 : 16 ≤ D.R.m ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm 4
  have hf16 : 16 ≤ D.R.f := le_trans hm4 hmf
  have hk16 : 16 ≤ D.R.k := le_trans hf16 hfk
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hfR : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hkR : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16
  have hL : (1 : ℝ) ≤ L := hL1.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hmR 5
    unfold mfL
    calc (5 : ℝ) ≤ 32 * 16 * 1 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 5 * D.R.f * L := by
        apply mul_le_mul (mul_le_mul hm5 hfR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)
  · have hb : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hkg : ∀ g : ℝ, ((D.R.k : ℝ) * Real.exp L) ^ 8 ≤ g → (D.R.k : ℝ) ^ 8 ≤ g := fun g hg =>
      le_trans (pow_le_pow_left₀ (by positivity) (le_mul_of_one_le_right (by positivity) hb) 8) hg
    have h0 : D.R.k ^ 8 ≤ D.host.g 0 := by exact_mod_cast hkg _ hg0
    have h1 : D.R.k ^ 8 ≤ D.host.g 1 := by exact_mod_cast hkg _ hg1
    set N := (D.host.g 0 * D.host.g 1) ^ 2 with hNdef
    have hk8 : 4 * D.R.f ≤ D.R.k ^ 8 := by
      calc 4 * D.R.f ≤ D.R.k * D.R.k := Nat.mul_le_mul (by omega) hfk
        _ = D.R.k ^ 2 := (sq _).symm
        _ ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hkpos : 1 ≤ D.R.k ^ 8 := Nat.one_le_pow _ _ (by omega)
    have hgg : D.R.k ^ 8 ≤ D.host.g 0 * D.host.g 1 :=
      le_trans h0 (Nat.le_mul_of_pos_right _ (by omega))
    have hNge : D.host.g 0 * D.host.g 1 ≤ N := by
      rw [hNdef, sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hN4 : 4 * D.R.f ≤ N := le_trans hk8 (le_trans hgg hNge)
    have hN2 : 2 ≤ N := by omega
    obtain ⟨-, hmod⟩ := hT u
    rw [Nat.one_mod_eq_one.mpr (by omega)] at hmod
    have hTp := (D.mem u).A.T_prime
    have h2 := hTp.two_le
    have hdiv := Nat.div_add_mod ((D.mem u).A.T) N
    rw [hmod] at hdiv
    have hq : (D.mem u).A.T / N ≠ 0 := by
      intro hq0; rw [hq0] at hdiv; omega
    have : N ≤ N * ((D.mem u).A.T / N) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq)
    omega
  · rw [d0_eq]; exact hdu u
  · calc (5 : ℝ) ≤ 16 * 16 * 1 := by norm_num
      _ ≤ (D.R.f : ℝ) * D.R.k * L :=
        mul_le_mul (mul_le_mul hfR hkR (by norm_num) (by positivity)) hL (by norm_num) (by positivity)

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.ChainOnto.TameRes

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_ltOne (P : HeightOneSpectrum (𝓞 E)) :
    IsOpen {z : P.adicCompletion E | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion E) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

theorem val_alg (P : HeightOneSpectrum (𝓞 E)) (k : E) :
    Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

theorem valuation_eq_one_of_not_mem (P : HeightOneSpectrum (𝓞 E)) (s : 𝓞 E) (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
  le_antisymm (P.valuation_le_one s) (not_lt.mp fun h => hs ((P.valuation_lt_one_iff_mem s).mp h))

theorem locK_eq_one (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (c : (kP PP)ˣ →* ℂˣ)
    (hc : IsRes H PP c) (k : D.host.Eˣ) (hk : PP.valuation D.host.E ((k : D.host.E) - 1) < 1) :
    H.locK PP k = 1 := by
  have hv1 : PP.valuation D.host.E (k : D.host.E) = 1 := by
    have e : (k : D.host.E) = 1 + ((k : D.host.E) - 1) := by ring
    have h1 : PP.valuation D.host.E ((k : D.host.E) - 1) < PP.valuation D.host.E 1 := by rwa [map_one]
    rw [e]
    first
      | rw [Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_right _ h1, map_one]
      | rw [add_comm, Valuation.map_add_eq_of_lt_left _ h1, map_one]
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer (k : D.host.E) hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := by
    intro hm
    have hlt : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) < 1 :=
      (PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm
    exact absurd hav (ne_of_lt hlt)
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hdiff : a - (s : 𝓞 D.host.E) ∈ PP.asIdeal := by
    apply (PP.valuation_lt_one_iff_mem (K := D.host.E) _).mp
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E (a - (s : 𝓞 D.host.E))) < 1
    rw [map_sub, ← h, ← sub_one_mul, map_mul, hsv, mul_one]
    exact hk
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have hms : (Ideal.Quotient.mk PP.asIdeal (s : 𝓞 D.host.E) : kP PP) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hms
  let u : (kP PP)ˣ := Units.mkOfMulEqOne _ b hb
  let ka : D.host.Eˣ := Units.mk0 _ ha0
  let ks : D.host.Eˣ := Units.mk0 _ hs0
  have e1 : c u = H.locK PP ks := hc (s : 𝓞 D.host.E) ks u rfl rfl
  have e2 : c u = H.locK PP ka := hc a ka u rfl (Ideal.Quotient.eq.mpr hdiff).symm
  have hk' : k = ka * ks⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ka, ks]
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hk', map_mul, map_inv, ← e1, ← e2, mul_inv_cancel]

theorem tameAt_of_isRes : ∀ (D : D7) (H : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ),
    IsRes H PP a → H.TameAt PP := by
  intro D H PP c hc
  unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
  intro x _ hx1
  by_contra hne
  have hcont : Continuous (H.loc PP) := H.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele PP)
  have hW : IsOpen {y : (PP.adicCompletion D.host.E)ˣ | H.loc PP y ≠ 1} := isOpen_ne_fun hcont continuous_const
  obtain ⟨T, hT, hTe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hW
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hxT : (x : PP.adicCompletion D.host.E) ∈ T ∩ {z | Valued.v (z - 1) < 1} := by
    refine ⟨?_, lt_of_le_of_lt hx1 hlt⟩
    have : x ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := by rw [hTe]; exact hne
    exact this
  have hU : IsOpen (T ∩ {z : PP.adicCompletion D.host.E | Valued.v (z - 1) < 1}) :=
    hT.inter ((isOpen_ltOne PP).preimage (continuous_sub_right 1))
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨_, hxT⟩
  have hk1 : PP.valuation D.host.E (k - 1) < 1 := by
    rw [← val_alg, map_sub, map_one]; exact hk.2
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk1
  have hloc := locK_eq_one D H PP c hc (Units.mk0 k hk0) hk1
  have hmem : Formalism.L2.Host.atFin PP (Units.mk0 k hk0) ∈ (Units.val ⁻¹' T : Set (PP.adicCompletion D.host.E)ˣ) := hk.1
  rw [hTe] at hmem
  exact hmem hloc

end GlobalTheory.ChainOnto.TameRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueEqDivMul
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem holValueAt_eq_div_mul : ∀ (Z L d Y : ℂ → ℂ) (s₀ z l : ℂ) (s₁ : ℝ), 0 < s₀.re → s₁ < s₀.re → AnalyticOnNhd ℂ d (rightOf 0) → (∀ s : ℂ, 0 < s.re → d s ≠ 0) → DifferentiableOn ℂ Y (rightOf s₁) → EqRight Z (fun s => L s / d s * Y s) → HolValueAt Z s₀ z → HolValueAt L s₀ l → z = l / d s₀ * Y s₀ := by
  intro Z L d Y s₀ z l s₁ h0 h1 hd hd0 hY e hZ hL
  exact (hZ.congr e).unique ((hL.div (holValueAt_self hd h0) (hd0 _ h0)).mul
    (holValueAt_self (hY.analyticOnNhd (isOpen_rightOf s₁)) h1))

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HostTieTrueCols
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem host_tie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (B.primes X) := by
  intro B X I h l Z L
  have hX : B.fields.Ok := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := host_fields_primes_ties I h hX l Z
  refine ⟨rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, fun _ => rfl, HEq.rfl⟩
  · rw [h9]
    rfl
  · intro i; rw [h10]; rfl
end GlobalTheory.CoreHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRationStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricLevels_characters_doubleCosets_agree_rational : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → LevelAgree Ch sel mu cst σ₀ P ι s W := by
  first | exact @GlobalTheory.TwBridge.Lev.levelAgree | exact GlobalTheory.TwBridge.Lev.levelAgree | (intros; apply GlobalTheory.TwBridge.Lev.levelAgree <;> assumption)
end

