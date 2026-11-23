module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevOfRed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SeeSaw.RedLev

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := by
  simp [Formalism.L2.DIV.frGL]

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1000000 in
theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul (F := D.host.F) (E := D.host.E) β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_eq {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k n Y) (bas W : GL Y k) (σ : Fin n ≃ Y)
    (N : Matrix (Fin n) (Fin n) k)
    (h : F.β * W.val * F.γ * (F.β * bas.val).submatrix id σ = (F.β * bas.val).submatrix id σ * N) :
    (bas⁻¹ * W * bas).val.submatrix σ σ = N := by
  have h1 : ((bas⁻¹).val * F.γ).submatrix σ id * (F.β * bas.val).submatrix id σ = 1 := by
    change ((bas⁻¹).val * F.γ * (F.β * bas.val)).submatrix σ σ = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Units.inv_mul, Matrix.submatrix_one_equiv]
  rw [← Matrix.one_mul N, ← h1, Matrix.mul_assoc, ← h]
  change _ = ((bas⁻¹).val * F.γ * (F.β * W.val * F.γ * (F.β * bas.val))).submatrix σ σ
  congr 1
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.γ F.β bas.val, ← Matrix.mul_assoc F.γ F.β, F.γβ, Matrix.one_mul, Matrix.one_mul]

end

end GlobalTheory.SeeSaw.RedLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwMovedVal


set_option maxHeartbeats 4000000 in
theorem moves_rep_tw : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} (A : TwDat I l Z u a Ch), A.Is → ∀ (j : ℕ) (hj : j ≤ B.R.m) (c : (I.stp u a j).Cl) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), finM _ (rankN (I.rec7 l Z) j hj) g = ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 → Moves _ (rankN (I.rec7 l Z) j hj) g ((I.stp u a j).rep c).1.1.deco.1.N := by
  intro B X I l Z u a Ch A hA j hj c g hg
  have h1 := ((hA.reads j hj).pt c).lat
  have h2 := ((hA.base j hj (A.chOf j c)).1).lat
  rw [extTo_deco] at h1 h2
  rw [(hA.base j hj (A.chOf j c)).2] at h2
  have hinv : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ = ((((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1)⁻¹ : GL _ _).1 := by
    have e1 : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ * ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 = 1 := by
      rw [← hg, ← GlobalTheory.RepLattice.finM_mul', inv_mul_cancel, GlobalTheory.RepLattice.finM_one']
    rw [← Matrix.mul_one (finM _ _ g⁻¹), ← Units.mul_inv (((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1), ← Matrix.mul_assoc, e1,
      Matrix.one_mul]
  intro x
  rw [hinv]
  let p := ((I.stp u a j).rep c).1.1
  have hspan : Submodule.span B.fields.E (p.deco.1.N : Set (Formalism.L2.Col.Sp B.fields.E (B.R.N j))) = ⊤ := by
    open Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col in
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E _ v = f := by
      apply (Pi.basisFun B.fields.E _).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ p.deco.1.N := by
      rw [← show dual (hStd B.fields.E _) p.deco.1.N = p.deco.1.N from p.deco.2.uni, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E _ v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E _ y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : (Formalism.L2.Col.Sp B.fields.E (B.R.N j)) →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : p.deco.1.N.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ p.deco.2.lat.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  have hfull : Submodule.IsFullLattice B.fields.E p.deco.1.N :=
    { toIsLattice := p.deco.2.lat, span_eq_top := hspan }
  exact GlobalTheory.RepLattice.mem_iff_of_carries _ _ _ hfull h1 h2 x


set_option maxHeartbeats 1600000 in
theorem moved_datum_val_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}), Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (A.h i α c) ((I.stp u a i).rep c.1).1.1.deco.1.N ∧ Moves _ (rankN (I.rec7 l Z) (i + 1) hi) (A.h (i + 1) γ c') ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N ∧ ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, Φ (actO _ _ (A.h i α c)⁻¹ (A.h (i + 1) γ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = p * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hOk hP l Z u a Ch A hA i hi α γ Φ hΦ p hΦv c c'
  obtain ⟨c, rfl⟩ := c
  obtain ⟨c', rfl⟩ := c'
  obtain ⟨hg, hy⟩ := hA.h i (Nat.le_of_succ_le hi) (A.chOf i c) ⟨c, rfl⟩
  obtain ⟨hg', hy'⟩ := hA.h (i + 1) hi (A.chOf (i + 1) c') ⟨c', rfl⟩
  refine ⟨moves_rep_tw A hA i _ c _ hy, moves_rep_tw A hA (i + 1) hi c' _ hy', fun z => ?_⟩
  obtain ⟨M, hM0, hM⟩ := _root_.GlobalTheory.AdForm.TwResid.tw_resid_datum I hOk hP l Z u a Ch A hA i hi c c' _ _ hg hg' hy hy'
  obtain ⟨-, k, hk0, hkinv, -⟩ := hΦ
  obtain ⟨γ₀, v, hv, hvh, he⟩ := GlobalTheory.AdForm.exists_rat_half_approx _ _ A.e _ hA.idem (M * k) (Nat.mul_pos hM0 hk0)
    (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r))
  have hx : actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) =
      A.e • actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r) := by
    have : (z.map fun r => A.e * incA (I.rec7 l Z) r) = A.e • (z.map fun r => incA (I.rec7 l Z) r) := by
      ext a b; rfl
    simp only [actO, this, Matrix.mul_smul, Matrix.smul_mul]
  have half : ∀ (n : ℕ) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), IsHalf A.e v → IsHalf A.e (n • v) :=
    fun n v h a b => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, h a b]
  have e1 : Φ (γ₀.map fun r => A.e * incA (I.rec7 l Z) r) =
      Φ (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) := by
    rw [he, ← hx, mul_nsmul]
    exact hkinv _ (nsmul_mem hv M) (half M v hvh) _
  rw [← e1, hΦv]
  congr 1
  refine hM z γ₀ (k • v) (nsmul_mem hv k) (half k v hvh) ?_
  rw [he, ← hx, mul_nsmul']

end GlobalTheory.AdForm.TwMovedVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdealQuot

theorem intAt_mul {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  have hx := ha.2
  have hy := hb.2
  generalize finPart D a = x at hx
  generalize finPart D b = y at hy
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem commRing_rearrange_idempotent_fixed_product {R : Type*} [CommRing R] (Y X P Q ε s : R) (e2 : P * Q = Y * X) (hse : ε * s = s) :
    Y * (s * (X * ε)) = P * (Q * s) := by
  linear_combination (Y * X) * hse - s * e2

theorem commGroup_mul_mul_eq_mul_mul_div {R : Type*} [CommRing R] (Y P Q C s a : R) (e2 : P * Q * C = Y) :
    Y * (s * a) = P * ((Q * s) * (C * a)) := by
  linear_combination (-(s * a)) * e2

theorem unit_of_gen {D : D7} {v : Pl D} {c : D.host.E} (hc : c ≠ 0)
    (h : ∀ s, s ∈ idV (1 : FI D) v ↔ incA D c⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v)) (t : AE D) :
    (t ∈ intAt D (· = v) → incA D c⁻¹ * t ∈ intAt D (· = v)) ∧
      (t ∈ intAt D (· = v) → incA D c * t ∈ intAt D (· = v)) := by
  refine ⟨fun ht => ((h t).1 ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v t).2 ht)).1, fun ht => ?_⟩
  have h1 : incA D c * t ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ ht.1
  have h2 : incA D c⁻¹ * (incA D c * t) = t := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  exact (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 ((h _).2 ⟨by rw [h2]; exact ht, h1⟩)

theorem mul_subset_iff : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D), 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v),
    (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v := by
  intro D v 𝔞 𝔟 h𝔞 h𝔟 s hs
  obtain ⟨x, hx, gx⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  obtain ⟨y, hy, gy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔟 h𝔟
  obtain ⟨z, hz, gz⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h𝔞)
  have gyz := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔟 𝔞⁻¹ y z hy hz gy gz
  have gxz := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ x z hx hz gx gz
  rw [mul_inv_cancel₀ h𝔞] at gxz
  have hxz : x * z ≠ 0 := mul_ne_zero hx hz
  have u := unit_of_gen hxz gxz
  obtain ⟨ε, -, -, hε, hεa, -⟩ := (GlobalTheory.FinPl.localComponents D (· = v)).1
  rw [gyz]
  constructor
  · intro H
    have hxε : incA D x * ε ∈ idV 𝔞 v := by
      refine (gx _).2 ⟨?_, Ideal.mul_mem_left _ _ hε.1⟩
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]
    have h1 := ((gy _).1 (H _ hxε)).1
    have e1 : incA D y⁻¹ * (s * (incA D x * ε)) = incA D (x * z) * (incA D (y * z)⁻¹ * s) := by
      have hse : ε * s = s := (hεa s).1 hs
      have e2 : incA D (x * z) * incA D (y * z)⁻¹ = incA D y⁻¹ * incA D x := by
        rw [← map_mul, ← map_mul]; congr 1; field_simp
      exact commRing_rearrange_idempotent_fixed_product _ _ _ _ _ _ e2 hse
    rw [e1] at h1
    refine ⟨?_, hs⟩
    have := (u _).1 h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hxz, map_one, one_mul] at this
  · rintro ⟨H, -⟩ a ha
    obtain ⟨ha1, ha2⟩ := (gx a).1 ha
    refine (gy _).2 ⟨?_, Ideal.mul_mem_right _ _ hs⟩
    have e1 : incA D y⁻¹ * (s * a) = incA D (x * z) * ((incA D (y * z)⁻¹ * s) * (incA D x⁻¹ * a)) := by
      have e2 : incA D (x * z) * incA D (y * z)⁻¹ * incA D x⁻¹ = incA D y⁻¹ := by
        rw [← map_mul, ← map_mul]; congr 1; field_simp
      exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _ _ _ e2
    rw [e1]
    exact (u _).2 (intAt_mul H ha1)

end GlobalTheory.IdealQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PkOf

section Heq

open _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7}

theorem mu_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.μ = S1.μ := by
  subst h
  cases eq_of_heq hS
  rfl

end Heq

theorem natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ PP.asIdeal) : (n : 𝓞 E) ∉ PP.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hp)

theorem exists_of_mem_QE {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {PP : HeightOneSpectrum (𝓞 X.E)} (h : PP ∈ Formalism.L2.Col.QE sel ξ) : ∃ v, PP = sel v := by
  classical
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨v, rfl⟩
  · simp at h

end GlobalTheory.Fam.PkOf

namespace GlobalTheory.Fam

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isThetaFunO_annih_of_std {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {A B : HSp D} {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨)
    (τ : D.what₂.Tau)
    (J : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ → Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) :
    IsThetaFunO ψ (dblSp A) B (annih (heisO ψ (dblSp A) B) θ τ J z f) := by
  have h1 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf
  have h2 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf
  have h3 := (_root_.GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν _ _ h2 h2 Complex.I).2.1
  exact (_root_.GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν _ _ h1 h3 Complex.I).1

theorem sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsFockVec ψ θ (dblSp A) B s' sB f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hS : sch ψ A B ν 𝓨 f ∈ schwartzA θ B.rank A.rank :=
    (_root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ hψ θ hθ A B ν 𝓨 hν).1 f hth
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact _root_.GlobalTheory.StdUnnAnnih.annih_sch D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  have hz : sch ψ A B ν 𝓨 0 = 0 := by
    have h := (_root_.GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hν f f hth hth 0).2.2.2
    rwa [zero_smul, zero_smul] at h
  refine _root_.GlobalTheory.StdUnn.FockSlice.mem_fockA_of_slices D θ hθ B A.rank l sB _ hS
    (_root_.GlobalTheory.StdUnn.Slice.slice_polyGauss D θ hθ B A.rank l sB hsB N _ hS ?_)
  intro L hL
  rw [← (key L).2, hN _ (by rw [List.length_map, hL]), hz]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  first | exact @GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | exact GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | (intros; apply GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lineStable_lattice_splitsAlongWitt_selfDualCore : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S), IsSelfDualC S L → (∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) → IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | exact GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.selfDual_core_monoAt <;> assumption)
end

