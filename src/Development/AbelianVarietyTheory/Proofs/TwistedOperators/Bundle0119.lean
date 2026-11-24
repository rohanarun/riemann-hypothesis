module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0088
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallS
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.DeepPoint


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_one (I : AutInst) (m : ℕ) : (1 : I.Gf) ∈ I.Kg m :=
  ⟨K_one I, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_mul (I : AutInst) (m : ℕ) {x y : I.Gf} (hx : x ∈ I.Kg m) (hy : y ∈ I.Kg m) : x * y ∈ I.Kg m := by
  refine ⟨K_mul I hx.1 hy.1, fun v hv => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hy.2 v hv
  obtain ⟨z', hz', hxz⟩ := hx.2 v hv
  refine ⟨I.fmat x *ᵥ z + z', add_mem (K_mv I hx.1 hz) hz', ?_⟩
  have e : (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  rw [e, hyz, hxz, Matrix.mulVec_smul, smul_add]


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_inv (I : AutInst) (m : ℕ) {k : I.Gf} (hk : k ∈ I.Kg m) : k⁻¹ ∈ I.Kg m := by
  refine ⟨K_inv I hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv I (K_inv I hk.1) hz), ?_⟩
  have h1 : I.fmat k⁻¹ * I.fmat k = 1 := fmat_inv_mul I k
  have e : (I.fmat k⁻¹ - 1) *ᵥ y = -(I.fmat k⁻¹ *ᵥ ((I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem isIsot_span (I : AutInst) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (hiso : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) :
    I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  first
  | exact @_root_.GlobalTheory.HermitianFormLinearity.main
  | exact _root_.GlobalTheory.HermitianFormLinearity.main
  | (apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianFormLinearity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianFormLinearity.main ..)

theorem exists_step (I : AutInst) (x : I.GA) (q : ℕ) (hn : 1 ≤ I.n)
    (hrk : ∀ v, rkR (I.ε v) ≤ q) (hl : least I x < 1 / 2) :
    ∃ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ),
      IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R ∧ R ≠ ⊥ ∧ R ≤ stepLt I x (1 / 2) ∧
      R ≤ lamX I x ∧ 0 < hi ∧ largestSize (bas I) (frm I x) R ≤ hi ∧
      (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) ∧
      hi ≤ (2 * least I x) ^ ((1 : ℝ) / q) * lo ∧ hi ^ 2 ≤ (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  have hpiece := (hspec a S τ hF).1
  have ha0 := ((hspec a S τ hF).2 hn).1
  have hτ0 := ((hspec a S τ hF).2 hn).2
  obtain ⟨hS0, hSmono, hSlast, hτmono, hτ, -⟩ := hF
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hl)
    · exact h
  have hrkS : ∀ i : Fin (a + 1), (i : ℕ) ≤ rkK (S i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have := (hpiece i).2.1
      simp only [Fin.coe_castSucc] at ih
      simp only [Fin.val_succ]
      omega
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 := hrkS (Fin.last a)
    rw [hSlast] at h1
    have h2 := (GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
    simp only [Fin.val_last] at h1
    exact h1.trans (h2.trans (hrk v))
  set τ' : ℕ → ℝ := fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 with hτ'
  have hτ'pos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    simp only [hτ']
    split_ifs with h
    · exact (hτ ⟨i, h⟩).1
    · norm_num
  have hτ'lt : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    simp only [hτ', dif_pos hi]
    split_ifs with h
    · exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · exact (hτ ⟨i, hi⟩).2.1
  have hτ'a : τ' a = 1 / 2 := by simp [hτ']
  have hτ'0 : τ' 0 = least I x := by
    simp only [hτ', dif_pos (show 0 < a by omega)]
    exact hτ0 (by omega)
  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hτ'pos hτ'lt hτ'a
  rw [hτ'0] at hratio hsq
  set i : Fin a := ⟨b, hb⟩ with hi_def
  have hib : τ' b = τ i := by simp [hτ', hb, i]
  refine ⟨S i.succ, τ' (b + 1), τ i, ?_, ?_, ?_, ?_, (hτ i).1, ?_, ?_, ?_, ?_⟩
  · rw [(hτ i).2.2.1]; exact (GlobalTheory.CountSteps.steps I x _ (hτ i).1).1
  · intro h
    have := hSmono (Fin.succ_pos i)
    rw [hS0, h] at this
    exact lt_irrefl _ this
  · rw [← hSlast]; exact hSmono.monotone (Fin.le_last _)
  · rw [(hτ i).2.2.1]; exact sSup_le fun N hN => hN.1
  · exact (hpiece i).2.2.1.le
  · intro N hN hNL
    by_cases hb1 : b + 1 < a
    · have eS : S i.succ = S (Fin.castSucc (⟨b + 1, hb1⟩ : Fin a)) := congrArg S (Fin.ext (by simp [i]))
      have e : τ' (b + 1) = τ ⟨b + 1, hb1⟩ := by simp [hτ', hb1]
      rw [e, eS]
      rw [eS] at hN
      exact (hpiece ⟨b + 1, hb1⟩).2.2.2.1 N hN hNL
    · have hba : b + 1 = a := by omega
      have e : τ' (b + 1) = 1 / 2 := by rw [hba, hτ'a]
      have eS : S i.succ = stepLt I x (1 / 2) := by
        rw [← hSlast]; exact congrArg S (Fin.ext (by simp [i, hba]))
      rw [e, eS]
      rw [eS] at hN
      exact (GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hN hNL
  · rw [← hib]
    have hpos := hτ'pos (b + 1) (by omega)
    rwa [div_le_iff₀ hpos] at hratio
  · rw [← hib]; exact hsq

theorem deep_point : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n →
    (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset,
      ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ),
        (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧
        (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧
        Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤
          (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  intro I x g q hg _ hn hrk hl
  obtain ⟨R, lo, hi, hsat, hR0, hRS, hRL, hhi, hlarge, hlo, hhl, hh2⟩ := exists_step I x q hn hrk hl
  have hisoR : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 :=
    fun y hy z hz => (GlobalTheory.FlagIso.flag_isotropic I x).1 y (hRS hy) z (hRS hz)
  have hperp : R ≤ perpIn I x R := fun y hy =>
    Submodule.subset_span ⟨hRL hy, fun s hs => hisoR s hs y hy⟩
  have hWiso : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := isIsot_span I R hR0 hisoR
  refine ⟨_, hWiso, fun m hm => ?_⟩
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I _ hWiso
  have hU : {c : I.Gf | x.2⁻¹ * c * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have ho : IsOpen (I.Kg g) := I.topf_open g hg
    have hc : Continuous fun c : I.Gf => x.2⁻¹ * c * x.2 :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine (ho.preimage hc).mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel]
    exact kg_one I g
  obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
  have hm'N : γ⁻¹ * m ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
    rw [← hN] at hγN hm ⊢
    exact N.mul_mem (N.inv_mem hγN) hm
  have hν := (hsplit _ hm'N).1
  obtain ⟨γ', ⟨hγ'F, -⟩, hγ'K, A, Z, hAZ, heq, hbd, -⟩ :=
    GlobalTheory.SmallFund.small_fundamental_set I x g R lo hi _ hg hsat hR0 hperp hhi hlarge hlo hhl hh2 _ hν
  have hk : (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2) ∈ I.Kg g :=
    kg_mul I g (kg_inv I g hγ'K) hγU
  refine ⟨γ * γ', Formalism.MainNotions.LeviCoordinates.rrg_mul_mem I hγF hγ'F, _, hk,
    (γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1, A, Z, hAZ, fun v => ?_, ?_, hbd⟩
  · have e : uMat (((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1) v) =
        uMat ((γ'.1 v * x.1 v)⁻¹) * (uMat ((γ⁻¹ * m).1 v) * uMat (x.1 v)) := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_assoc]
      rfl
    rw [e, heq v]
    have e2 : uMat (γ'.1 v) * uMat (x.1 v) = uMat (γ'.1 v * x.1 v) := rfl
    have e3 : uMat ((γ'.1 v * x.1 v)⁻¹) * uMat (γ'.1 v * x.1 v) = 1 := by
      show uMat ((γ'.1 v * x.1 v)⁻¹ * (γ'.1 v * x.1 v)) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat ((γ'.1 v * x.1 v)⁻¹)), e3, Matrix.one_mul]
  · have h2 : γ' * x * ((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1,
        (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2)) = (γ⁻¹ * m) * x := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv]
        group
    calc m * x = γ * ((γ⁻¹ * m) * x) := by group
      _ = γ * γ' * x * _ := by rw [← h2]; simp only [mul_assoc]

end GlobalTheory.DeepPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvIdempotentAct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

theorem act_sum_smul {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (g : Formalism.L2.DIV.G0 L.Pg L.r) {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → GA D V → ℂ) :
    actG0 V β L g (∑ i ∈ s, c i • F i) = ∑ i ∈ s, c i • actG0 V β L g (F i) := by
  unfold actG0
  split_ifs with hk
  · funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  · simp

theorem convIdempotent_act : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) [Fintype (Formalism.L2.DIV.G0 L.Pg L.r)], LiftsExist V β L → ∀ c : Formalism.L2.DIV.G0 L.Pg L.r → ℂ, (∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) → ∀ F : GA D V → ℂ, HasType V β (flag1L L) F → (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F)) = ∑ g, c g • actG0 V β L g F := by
  intro D V β L _ hL c hc F hF
  have hA := levelGroupAction_isAction V β L hL F hF
  calc (∑ g, c g • actG0 V β L g (∑ g', c g' • actG0 V β L g' F))
      = ∑ g, ∑ g', (c g * c g') • actG0 V β L (g * g') F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [act_sum_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun g' _ => ?_
        rw [hA.2 g g', smul_smul]
    _ = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun g' => by
          simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • actG0 V β L k F := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_smul.symm
    _ = ∑ g, c g • actG0 V β L g F := by
        simp only [hc]

end GlobalTheory.FlagAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCovBySubmodule
section
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubquot

theorem exists_covBy_submodule {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    ∃ S T : Submodule R M, T ⋖ S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  haveI := CompleteLattice.Iic_coatomic_of_compact_element (Submodule.singleton_span_isCompactElement (R := R) m)
  rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Set.Iic (Submodule.span R {m})) with h0 | ⟨c, hc, -⟩
  · have h1 : (⊥ : Submodule R M) = Submodule.span R {m} := congrArg Subtype.val h0
    exact absurd (Submodule.mem_span_singleton_self m) (by rw [← h1]; simpa using hm)
  · refine ⟨Submodule.span R {m}, c.1, lt_of_le_of_ne c.2 fun h => hc.1 (Subtype.ext h), ?_⟩
    intro x h1 h2
    have := congrArg Subtype.val (hc.2 ⟨x, h2.le⟩ h1)
    exact h2.ne this

theorem exists_irreducible_subquotient : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Nontrivial V → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ G Y), σ.IsIrreducible ∧ IsSubquotient σ ρ := by
  intro G _ V _ _ ρ hV
  haveI : Nontrivial ρ.asModule := hV
  obtain ⟨S, T, h⟩ := exists_covBy_submodule (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h' : e.symm T ⋖ e.symm S :=
    ⟨e.symm.lt_iff_lt.2 h.1, fun c h1 h2 => h.2 (c := e c) (by simpa using e.lt_iff_lt.2 h1)
      (by simpa using e.lt_iff_lt.2 h2)⟩
  refine ⟨_, _, _, subQuot (e.symm S) (e.symm T), isIrreducible_subQuot h', e.symm S,
    ⟨Submodule.mkQ _, fun g => ?_⟩, Submodule.mkQ_surjective _⟩
  ext x
  rfl

end GlobalTheory.IrrSubquot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaClosed

open GlobalTheory.FinTranslate

variable {D : D7}

theorem finPart_eInf_smul (a : Formalism.L2.Theta.AE D) : finPart D (eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq]
    have h0 : sndA D.host.F (eInf D) = 0 := rfl
    rw [smul_eq_mul, map_mul, h0, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]

theorem infPart_one_sub_eInf_smul (a : Formalism.L2.Theta.AE D) : infPart D ((1 - eInf D) • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
      id_eq]
    have h1 : fstA D.host.F (eInf D) = 1 := rfl
    rw [smul_eq_mul, map_mul, map_sub, map_one, h1, sub_self, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]

theorem isThetaFunO_heisO_all {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) : IsThetaFunO ψ S T (heisO ψ S T u f) := by

  have hre : (eInf D • u).map (finPart D) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, finPart_eInf_smul]
  have hfin : ((1 - eInf D) • u).map (infPart D) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, infPart_one_sub_eInf_smul]
  have hsplit : (1 - eInf D) • u + eInf D • u = u := by
    rw [sub_smul, one_smul, sub_add_cancel]

  have hcomp : heisO ψ S T ((1 - eInf D) • u) (heisO ψ S T (eInf D • u) f) = heisO ψ S T u f := by
    rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_fin_real hfin hre, AddChar.map_zero_eq_one, one_smul,
      hsplit]
  rw [← hcomp]
  exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hre hf) hfin

theorem thetaClosed : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ u, IsThetaFunO ψ S T (heisO ψ S T u f)) ∧ ∀ τ z, IsThetaFunO ψ S T (Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ hψ hθ S T f hf
  exact ⟨fun u => isThetaFunO_heisO_all hψ hf u, fun τ z => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf⟩

end GlobalTheory.ThetaClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddings
section
open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory

theorem minpoly_coeff_le_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (w : InfinitePlace F) (j : ℕ) :
    w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E *
      ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  set M : ℝ≥0 := max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) with hM
  set p := minpoly F x
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h1 : p.Monic := minpoly.monic hx
  have hd : p.natDegree ≤ Module.finrank F E := minpoly.natDegree_le x
  have h3 : ∀ z ∈ (p.map w.embedding).roots, ‖z‖ ≤ (M : ℝ) := by
    intro z hz
    have hz' : z ∈ p.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨h1.ne_zero, ?_⟩
      have := (Polynomial.mem_roots (Polynomial.map_monic_ne_zero h1)).1 hz
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact this
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hz'
    obtain ⟨ψ, rfl⟩ := hz'
    let τ : EmbOver E w := ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
    have : ‖ψ x‖₊ ≤ M :=
      le_trans (Finset.le_sup (f := fun τ : EmbOver E w => ‖τ.1 x‖₊) (Finset.mem_univ τ)) (le_max_right _ _)
    exact_mod_cast this
  have key := Polynomial.coeff_le_of_roots_le (f := w.embedding) j h1 (IsAlgClosed.splits _) h3
  rw [Polynomial.coeff_map] at key
  have hw : w (p.coeff j) = ‖w.embedding (p.coeff j)‖ := (InfinitePlace.norm_embedding_eq w _).symm
  rw [hw]
  refine key.trans ?_
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left _ _
  have hpow : (M : ℝ) ^ (p.natDegree - j) ≤ (M : ℝ) ^ Module.finrank F E :=
    pow_le_pow_right₀ hM1 (le_trans (Nat.sub_le _ _) hd)
  have hch : ((p.natDegree.choose j : ℕ) : ℝ) ≤ 2 ^ Module.finrank F E := by
    have := (Nat.choose_le_two_pow p.natDegree j).trans (Nat.pow_le_pow_right (by norm_num) hd)
    exact_mod_cast this
  rw [mul_comm]
  exact mul_le_mul hch hpow (by positivity) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphic_rightTranslate_finite : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (κ : GA D V), κ ∈ GfC V → ∀ φ : GA D V → ℂ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V κ φ) := by
  first | exact @GlobalTheory.FinTranslate.isAutFunSm_rTr | exact GlobalTheory.FinTranslate.isAutFunSm_rTr | (intros; apply GlobalTheory.FinTranslate.isAutFunSm_rTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistAdelicTop

theorem locallyCompact_secondCountable_borel_countable :
    ∀ {D : D7} (V : HSp D), LocallyCompactSpace (GA D V) ∧ SecondCountableTopology (GA D V) ∧
      BorelSpace (GA D V) ∧ Countable (GQ V) := by
  intro D V
  obtain ⟨hlc, hsc, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  exact ⟨hlc, hsc, ⟨rfl⟩, (GlobalTheory.RationalCountable.discrete_countable_GQ D V).2⟩

end GlobalTheory.TwistAdelicTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcrete
section
namespace GlobalTheory.RegSSObj

theorem regularSemisimple : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple :=
  GlobalTheory.RegSS.regularSemisimple

end GlobalTheory.RegSSObj
end

