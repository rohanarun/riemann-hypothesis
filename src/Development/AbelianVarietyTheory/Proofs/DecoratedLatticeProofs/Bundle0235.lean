module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ItOnto
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt)
open GlobalTheory.Chain.IoLift

theorem kfin_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ = kFin M τ := Submodule.span_eq (kFin M τ)

theorem span_le_range {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) :
    Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} ≤ LinearMap.range (inclK h) := by
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ fun τ => ⟨(v τ : M.H τ), (kfin_eq M τ) ▸ hv τ⟩, ?_⟩
  rw [inclK_tprod]

theorem range_le_span {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : KSm M) (y : KT M) :
    inclK h y ∈ Submodule.span ℂ {w : SmT M | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v} := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [map_smul, inclK_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => (kfin_eq M τ).symm ▸ (u τ).2, rfl⟩)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem kfinSpan_le_span_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) ≤ Submodule.span ℂ {w | ∃ P, ∃ v ∈ (Submodule.span ℂ {w : SmT M' | ∃ v : (M').Vec, (∀ τ, (v τ : (M').H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M' τ) ∧ w = PiTensorProduct.tprod ℂ v}), w = It P v} := by
  intro hD hH D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  choose hs a ha hirr using fun τ => GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D V S M τ
  have h : KSm M := hs
  have h' : KSm M' := fun τ => (GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible hH D W S' M' τ).1
  have hval := _root_.GlobalTheory.ItKFin.itKFin D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt
  have inj := inclK_injective h
  obtain ⟨I, hI⟩ : ∃ I : PolF D W.rank V.rank →ₗ[ℂ] KT M' →ₗ[ℂ] KT M,
      ∀ φ y, inclK h (I φ y) = It φ (inclK h' y) := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 inj)
    refine ⟨(It.compl₂ (inclK h')).compr₂ g, fun φ y => ?_⟩
    obtain ⟨z, hz⟩ := span_le_range M h (hval φ (inclK h' y))
    change inclK h (g (It φ (inclK h' y))) = _
    rw [← hz, ← LinearMap.comp_apply g, hg, LinearMap.id_apply]
  obtain ⟨χS, χT, hω, hexp⟩ := hW
  have hL := fun τ => _root_.GlobalTheory.LieScalar.lieFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ (aS τ) (aT τ) hθ hω
    (hexp τ).1 (hexp τ).2 (isVacF_of_isVacVec hf)
  have hstep : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ, ∃ φ', ∀ y, intersection_update_fsHerm_neg_one τ (a τ X) (I φ y) = I φ' y := by
    intro τ X hX φ
    obtain ⟨φ', hd⟩ : ∃ φ', ∀ v, DerT M τ X (It φ v) (It φ' v) := ⟨_, hIt.eqg τ X hX φ _ ((hL τ).1 X hX φ)⟩
    refine ⟨φ', fun y => inj ?_⟩
    have e := hd (inclK h' y)
    rw [← hI] at e
    rw [hI]
    exact derT_unique ((GlobalTheory.Chain.IoLift.FinTensor.kFinTensor D V S M τ h).2.1 _ (ha τ) X hX _) e
  obtain ⟨N, hNd⟩ : ∃ N : Submodule ℂ (KT M), N = Submodule.span ℂ {x | ∃ φ y, I φ y = x} := ⟨_, rfl⟩
  have hN : ∀ τ (X : lieAt V τ), ∀ x ∈ N, intersection_update_fsHerm_neg_one τ (a τ X) x ∈ N := by
    intro τ X x hx
    rw [hNd] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, y, rfl⟩ := hx
      obtain ⟨φ', hφ'⟩ := hstep τ X X.2 φ
      exact Submodule.subset_span ⟨φ', y, (hφ' y).symm⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h0 : N ≠ ⊥ := by
    obtain ⟨φ, y, hne⟩ := _root_.GlobalTheory.Chain.IoLift.ItNe.exists_ne_zero_inclK hH D V W S S' M M' θ ω _ It hIt h'
    intro e
    refine hne ?_
    have : I φ y ∈ N := hNd ▸ Submodule.subset_span ⟨φ, y, rfl⟩
    rw [e, Submodule.mem_bot] at this
    rw [← hI, this, map_zero]
  have htop := _root_.GlobalTheory.TensorIrr.eq_top_of_stable D.what₂.Tau (fun τ => kFin M τ) (fun τ => lieAt V τ) (fun τ X => a τ X) hirr N hN h0
  intro w hw
  obtain ⟨z, rfl⟩ := span_le_range M h hw
  have hz : z ∈ N := htop ▸ Submodule.mem_top
  rw [hNd] at hz
  clear hw
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, y, rfl⟩ := hx
    exact Submodule.subset_span ⟨φ, inclK h' y, range_le_span M' h' y, (hI φ y)⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ItOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemBlockUpperTriangularTwoIffLowerLeftZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ParabIndex

theorem card_GL_real (κ : Type) [Field κ] [Finite κ] (m : ℕ) :
    (Nat.card (GL (Fin m) κ) : ℝ)
      = (Nat.card κ : ℝ) ^ (m * m) * ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  letI := Fintype.ofFinite κ
  rw [GlobalTheory.Mem.card_GL_eq_pow_mul_qE κ m, Nat.card_eq_fintype_card, Formalism.MainNotions.ZetaProductPairs.qE]
  congr 1
  have h : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [_root_.zpow_neg, zpow_natCast]

variable {κ : Type} [Field κ]

theorem val_mk' {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι κ) (h : IsUnit A.det) :
    ((Matrix.GeneralLinearGroup.mk'' A h : GL ι κ) : Matrix ι ι κ) = A := rfl

def toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) κ :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (g : Matrix (Fin (r + s)) (Fin (r + s)) κ)

theorem isUnit_det_toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : IsUnit (toSum g).det := by
  rw [toSum, Matrix.det_reindex_self]
  exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

theorem mem_blockUpperTriangularTwo_iff_lowerLeft_zero {r s : ℕ} (g : GL (Fin (r + s)) κ) :
    g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ (toSum g).toBlocks₂₁ = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h
    ext i j
    simp only [toSum, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, Matrix.zero_apply]
    apply h
    simp [Formalism.L2.DIV.blk2]
  · intro h i j hij
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
    rcases x with x | x <;> rcases y with y | y
    · simp [Formalism.L2.DIV.blk2] at hij
    · simp [Formalism.L2.DIV.blk2] at hij
    · have := congrFun (congrFun h x) y
      simpa [toSum, Matrix.toBlocks₂₁] using this
    · simp [Formalism.L2.DIV.blk2] at hij

theorem toSum_eq_fromBlocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    toSum g = Matrix.fromBlocks (toSum g).toBlocks₁₁ (toSum g).toBlocks₁₂ 0 (toSum g).toBlocks₂₂ := by
  rw [← (mem_blockUpperTriangularTwo_iff_lowerLeft_zero g).1 hg]; exact (Matrix.fromBlocks_toBlocks _).symm

theorem isUnit_blocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    IsUnit ((toSum g).toBlocks₁₁.det * (toSum g).toBlocks₂₂.det) := by
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (toSum g).toBlocks₁₂, ← toSum_eq_fromBlocks hg]
  exact isUnit_det_toSum g

theorem isUnit_det_fromBlocks {r s : ℕ} (A : GL (Fin r) κ) (D : GL (Fin s) κ) (B : Matrix (Fin r) (Fin s) κ) :
    IsUnit (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin s) (Fin s) κ))).det := by
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit)

noncomputable def blockTriangularEquiv (r s : ℕ) :
    Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r) ≃
      GL (Fin r) κ × GL (Fin s) κ × Matrix (Fin r) (Fin s) κ where
  toFun g :=
    (Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left (isUnit_blocks g.2)),
     Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right (isUnit_blocks g.2)),
     (toSum g.1).toBlocks₁₂)
  invFun x := ⟨Matrix.GeneralLinearGroup.mk'' _ (isUnit_det_fromBlocks x.1 x.2.1 x.2.2), by
    rw [mem_blockUpperTriangularTwo_iff_lowerLeft_zero]
    ext i j
    simp [toSum, Matrix.toBlocks₂₁, val_mk']⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = _
    have h := toSum_eq_fromBlocks g.2
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (toSum g.1).toBlocks₁₁ (toSum g.1).toBlocks₁₂ 0 (toSum g.1).toBlocks₂₂) = _
    rw [← h, toSum]
    simp
  right_inv x := by
    rcases x with ⟨A, D, B⟩
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_)
    · show (toSum _).toBlocks₁₁ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₁, val_mk']
    · show (toSum _).toBlocks₂₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₂₂, val_mk']
    · show (toSum _).toBlocks₁₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₂, val_mk']

theorem natCard_blockUpperTriangularTwo_finiteField (κ : Type) [Field κ] [Finite κ] (r s : ℕ) :
    Nat.card (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)) =
      Nat.card (GL (Fin r) κ) * Nat.card (GL (Fin s) κ) * Nat.card κ ^ (r * s) := by
  rw [Nat.card_congr (blockTriangularEquiv r s), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin s → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.ParabIndex

namespace GlobalTheory.ParabIndex

theorem index_maxParabolic_GL_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r s : ℕ), n = r + s → (((Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin n) κ)).index : ℕ) : ℝ) = (Nat.card κ : ℝ) ^ (r * s) * (∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) / ((∏ i ∈ Finset.Ioc 0 r, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) * ∏ i ∈ Finset.Ioc 0 s, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) := by
  intro κ _ _ n r s hn
  subst hn
  have hmul := (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).card_mul_index
  rw [natCard_blockUpperTriangularTwo_finiteField] at hmul
  have hR : (((Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).index : ℕ) : ℝ) *
      ((Nat.card (GL (Fin r) κ) : ℝ) * (Nat.card (GL (Fin s) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * s))
      = (Nat.card (GL (Fin (r + s)) κ) : ℝ) := by
    rw [mul_comm]; exact_mod_cast hmul
  have hGr : (Nat.card (GL (Fin r) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hGs : (Nat.card (GL (Fin s) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [card_GL_real] at hGr hGs
  rw [card_GL_real, card_GL_real, card_GL_real] at hR
  have hq : (Nat.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hPr := right_ne_zero_of_mul hGr
  have hPs := right_ne_zero_of_mul hGs
  rw [eq_div_iff (mul_ne_zero hPr hPs)]
  have key : (r + s) * (r + s) = r * r + s * s + r * s + r * s := by ring
  rw [key, pow_add, pow_add, pow_add] at hR
  have hX : (Nat.card κ : ℝ) ^ (r * r) * (Nat.card κ : ℝ) ^ (s * s) * (Nat.card κ : ℝ) ^ (r * s) ≠ 0 := by
    have := pow_ne_zero (r * r) hq; have := pow_ne_zero (s * s) hq; have := pow_ne_zero (r * s) hq
    positivity
  apply mul_right_cancel₀ hX
  linear_combination hR

end GlobalTheory.ParabIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFockSpaceOfPolynomialGaussianSlices
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.FockSlice

theorem exists_finset_inf_eq_iInf {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (U : I → Submodule K V) : ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

theorem exists_eval_recon {Y : Type} (W : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (S : Finset Y) (g' : Y → Y → ℂ), (∀ y, g' y ∈ W) ∧ ∀ g ∈ W, g = ∑ y ∈ S, g y • g' y := by
  classical
  let U : Y → Submodule ℂ W := fun y => LinearMap.ker ((LinearMap.proj y : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)
  obtain ⟨S, hS⟩ := exists_finset_inf_eq_iInf U
  let R : W →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun s => (LinearMap.proj (s : Y) : (Y → ℂ) →ₗ[ℂ] ℂ).comp W.subtype
  have hR : LinearMap.ker R = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hmem : w ∈ S.inf U := by
      rw [Submodule.mem_finsetInf]
      intro y hy
      have := congrFun hw ⟨y, hy⟩
      simpa [U, R] using this
    rw [hS, Submodule.mem_iInf] at hmem
    ext y
    simpa [U] using hmem y
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨S, fun y => if h : y ∈ S then (L (Pi.single ⟨y, h⟩ 1) : Y → ℂ) else 0, fun y => ?_, fun g hg => ?_⟩
  · by_cases h : y ∈ S
    · simp only [h, dite_true]; exact (L _).2
    · simp only [h, dite_false]; exact W.zero_mem
  · have h1 : (⟨g, hg⟩ : W) = L (R ⟨g, hg⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨g, hg⟩ = ∑ s : S, g s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [R, Finset.sum_apply, Pi.single_apply]
    have h3 := congrArg Subtype.val h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h3
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
    refine h3.trans ?_
    rw [← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [s.2]

end GlobalTheory.StdUnn.FockSlice

namespace GlobalTheory.StdUnn.FockSlice

theorem mem_fockA_of_slices : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), ∀ φ ∈ schwartzA θ V.rank n, (∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x)) → φ ∈ fockA θ V n l s := by
  intro D θ hθ V n l s φ hφ hslice
  classical
  obtain ⟨k, c, t, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose F G hG hFG using fun i => (t i).2
  let fin : Mx D V.rank n → (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun x i j => finPart D (x i j)
  let Pre : ((Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ) →ₗ[ℂ] (Mx D V.rank n → ℂ) :=
    LinearMap.funLeft ℂ ℂ fin
  let W : Submodule ℂ (Mx D V.rank n → ℂ) := Submodule.span ℂ (Set.range fun i => Pre (G i))
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  obtain ⟨S, g', hg'W, hrec⟩ := exists_eval_recon W
  have hWle : W ≤ (WeilM.SB _).map Pre := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨G i, hG i, rfl⟩)
  choose g'' hg''SB hg''eq using fun y => hWle (hg'W y)
  choose pt hpt _ using fun x y : Mx D V.rank n => _root_.GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hθ V.rank n (fun τ => compAt θ τ x) y
  choose p hp using hslice
  set Φ : Mx D V.rank n → ℂ := ∑ i, c i • (t i : Mx D V.rank n → ℂ) with hΦ
  have hΦx : ∀ x, Φ x = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x)) := by
    intro x
    simp only [hΦ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFG i]
  have hpt' : ∀ x y, Φ (pt x y) = ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) := by
    intro x y
    rw [hΦx]
    have e1 : (fun τ a b => compAt θ τ (pt x y) a b) = (fun τ a b => compAt θ τ x a b) := by
      funext τ a b; rw [(hpt x y).1 τ]
    have e2 : fin (pt x y) = fin y := by
      funext a b
      have := congrFun (congrFun (hpt x y).2 a) b
      simpa [fin, Matrix.map_apply] using this
    rw [e1, e2]
  have hG' : ∀ i x, G i (fin x) = ∑ y ∈ S, G i (fin y) * g' y x := by
    intro i x
    have := congrFun (hrec (Pre (G i)) (Submodule.subset_span ⟨i, rfl⟩)) x
    simpa [Pre, LinearMap.funLeft_apply, Finset.sum_apply, smul_eq_mul] using this
  have key : ∀ x, Φ x = ∑ y ∈ S, Φ (pt x y) * g' y x := by
    intro x
    rw [hΦx]
    calc ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin x))
        = ∑ i, ∑ y ∈ S, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x :=
          Finset.sum_congr rfl fun i _ => by
            rw [hG' i x, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ y ∈ S, ∑ i, c i * (F i (fun τ a b => compAt θ τ x a b) * G i (fin y)) * g' y x := Finset.sum_comm
      _ = ∑ y ∈ S, Φ (pt x y) * g' y x := Finset.sum_congr rfl fun y _ => by rw [hpt', Finset.sum_mul]
  have hfin : ∀ x y, (pt x y).map (finPart D) = y.map (finPart D) := fun x y => (hpt x y).2
  have hcomp : ∀ x y, (fun τ => compAt θ τ (pt x y)) = (fun τ => compAt θ τ x) := fun x y => funext (hpt x y).1
  have hEq : Φ = ∑ y ∈ S, (fun x => evalPoly (p y) (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g'' y (fun i j => finPart D (x i j))) := by
    funext x
    rw [key x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hp y (pt x y) (hfin x y), hcomp x y]
    congr 1
    rw [← hg''eq y]
    rfl
  rw [hEq]
  exact Submodule.sum_mem _ fun y _ => Submodule.subset_span ⟨p y, g'' y, hg''SB y, rfl⟩

end GlobalTheory.StdUnn.FockSlice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginWeilRepTargetEquivariant
section
namespace I195MixedCoordinates_d909b66b3061dc587285daac

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

end I195MixedCoordinates_d909b66b3061dc587285daac

public noncomputable abbrev _root_.I195MixedCoordinates_6a77e1566d048881366221d8.source :=
  @_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ValueAtOrigin

theorem mixS_zero_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ h f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source d) T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) ((_root_.I195MixedCoordinates_d909b66b3061dc587285daac.source d) T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hS hS₀ μ 𝓕 hμ h f hf
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · have hz := (_root_.GlobalTheory.Unf.mixRankZero D ψ).1 S S₀ T d μ 𝓕 hμ
    have hi := (_root_.GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ S S₀ T d hS.std).2.2.2 χS χT om om₀ hS hS₀ 1 h f hf
    change I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f 0)
    rw [hz, hz, hi, map_one]
  · obtain ⟨hsp, hrat, -, -, -, hmix, -⟩ := _root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    have hc := _root_.GlobalTheory.SameCharCompat.compatibleOfSameChar D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT χT om om₀ hS hS₀ μ 𝓕 (hrat ▸ hμ) h f hf
    have h0 : ∀ g : WO S T → ℂ, heisO ψ S T (d.extX T 0) g = g := by
      intro g; funext w
      simp [heisO, symplOH_zero_right]
    change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 (om (1, h) f) 0 = om₀ (1, h) (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0)
    rw [hmix, hmix, h0, h0, hc]

end GlobalTheory.ValueAtOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isHeight_hgtStd : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → IsHeight (hgtStd A a κ p) := by
  intro D A μ hμ κ hκ a p hc p₁ hp₁ α hα k hk
  have hq : κ.symm p₁ ∈ siegel A := (_root_.GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ (κ.symm p₁)).2 (by simpa using hp₁)
  set q : siegel A := ⟨κ.symm p₁, hq⟩ with hqdef
  have hk' : (p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hc]; simpa [mul_assoc] using hk
  have e : κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹ =
      ((q * p⁻¹ : siegel A) : GA D (dblSp A)) * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹) := by
    simp [hqdef, map_mul, mul_assoc]
  have hdet : aP A q = Matrix.GeneralLinearGroup.det α :=
    _root_.GlobalTheory.StdUnn.chart_aP_eq_det D A μ hμ κ hκ q α (by simpa [hqdef] using hα)
  show hgt A a (κ.symm (p₁ * k) * (p : GA D (dblSp A))⁻¹) * absA D (aP A p) = absA D (Matrix.GeneralLinearGroup.det α)
  rw [e, hgt_mul A a (q * p⁻¹) hk', ← map_mul, ← map_mul, inv_mul_cancel_right, hdet]

end GlobalTheory.StdUnn
end

