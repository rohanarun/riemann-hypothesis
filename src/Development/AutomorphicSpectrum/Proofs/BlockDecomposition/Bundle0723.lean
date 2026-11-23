module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCosetIndicatorSum
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

section CosetDecomp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem self_mem_cosetSet_decomp (t : ℕ) (c : k) (a : Fin t → k) : a ∈ cosetSet t c a := by
  show Multiplicative.ofAdd (a - a) ∈ Lc t c
  rw [sub_self, ofAdd_zero]
  exact (Lc t c).one_mem

theorem cosetSet_symm_decomp {t : ℕ} {c : k} {a b : Fin t → k} (h : a ∈ cosetSet t c b) :
    b ∈ cosetSet t c a := by
  have h' : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  show Multiplicative.ofAdd (b - a) ∈ Lc t c
  rw [← neg_sub, ofAdd_neg]
  exact (Lc t c).inv_mem h'

theorem cosetSet_trans_decomp {t : ℕ} {c : k} {a b d : Fin t → k} (h : a ∈ cosetSet t c b)
    (h' : b ∈ cosetSet t c d) : a ∈ cosetSet t c d := by
  have h1 : Multiplicative.ofAdd (a - b) ∈ Lc t c := h
  have h2 : Multiplicative.ofAdd (b - d) ∈ Lc t c := h'
  show Multiplicative.ofAdd (a - d) ∈ Lc t c
  rw [← sub_add_sub_cancel a b d, ofAdd_add]
  exact (Lc t c).mul_mem h1 h2

theorem exists_coset_reps (t : ℕ) (c : k) (S : Finset (Fin t → k)) :
    ∃ A : Finset (Fin t → k), (∀ s ∈ S, ∃ a ∈ A, s ∈ cosetSet t c a) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ∈ cosetSet t c b → a = b := by
  classical
  refine Finset.induction_on S ?_ ?_
  · exact ⟨∅, by simp, by simp⟩
  · intro x S _ ih
    obtain ⟨A, hcov, huniq⟩ := ih
    by_cases hex : ∃ a ∈ A, x ∈ cosetSet t c a
    · refine ⟨A, ?_, huniq⟩
      intro s hs
      rcases Finset.mem_insert.1 hs with hsx | hsS
      · rw [hsx]
        exact hex
      · exact hcov s hsS
    · push_neg at hex
      refine ⟨insert x A, ?_, ?_⟩
      · intro s hs
        rcases Finset.mem_insert.1 hs with hsx | hsS
        · exact ⟨x, Finset.mem_insert_self _ _, hsx ▸ self_mem_cosetSet_decomp t c x⟩
        · obtain ⟨a, ha, hsa⟩ := hcov s hsS
          exact ⟨a, Finset.mem_insert_of_mem ha, hsa⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with hax | haA
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hax, hbx]
          · rw [hax] at hab
            exact absurd hab (hex b hbA)
        · rcases Finset.mem_insert.1 hb with hbx | hbA
          · rw [hbx] at hab
            exact absurd (cosetSet_symm_decomp hab) (hex a haA)
          · exact huniq a haA b hbA hab

end CosetDecomp

theorem eq_sum_coset_indicators : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z) (c : k), c ≠ 0 → HasCompactSupport φ → (∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v) → ∃ A : Finset (Fin t → k), ∀ v, φ v = ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => φ a) v := by
  intro k _ _ _ _ t Z _ _ φ c _ hφ hinv
  classical
  have hval : ∀ a v, v ∈ cosetSet t c a → φ v = φ a := by
    intro a v hv
    have := hinv (Multiplicative.ofAdd (v - a)) hv a
    simpa using this
  have hopen : ∀ a, IsOpen (cosetSet t c a) := by
    intro a
    open ValuativeRel in
    have e : cosetSet t c a = ⋂ j, (fun v : Fin t → k => c * (v j - a j)) ⁻¹' ((𝒪[k] : Subring k) : Set k) := by
      ext v
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    rw [e]
    exact isOpen_iInter_of_finite fun j => (SplitWeil.isOpen_int k).preimage (by fun_prop)
  obtain ⟨S, hS⟩ := hφ.elim_finite_subcover (fun a : tsupport φ => cosetSet t c a) (fun a => hopen a)
    (fun v hv => Set.mem_iUnion.2 ⟨⟨v, hv⟩, self_mem_cosetSet_decomp t c v⟩)
  obtain ⟨A, hAcov, hAuniq⟩ := exists_coset_reps t c (S.image Subtype.val)
  refine ⟨A, fun v => ?_⟩
  by_cases hv : ∃ a ∈ A, v ∈ cosetSet t c a
  · obtain ⟨a, ha, hva⟩ := hv
    rw [Finset.sum_eq_single a]
    · rw [Set.indicator_of_mem hva]
      exact hval a v hva
    · intro b hb hba
      rw [Set.indicator_of_notMem]
      intro hvb
      exact hba (hAuniq b hb a ha (cosetSet_trans_decomp (cosetSet_symm_decomp hvb) hva))
    · intro haA
      exact absurd ha haA
  · push_neg at hv
    rw [Finset.sum_eq_zero]
    · by_contra hne
      have hvs : v ∈ tsupport φ := subset_tsupport _ hne
      obtain ⟨s, hsS, hvs'⟩ := Set.mem_iUnion₂.1 (hS hvs)
      obtain ⟨a, ha, hsa⟩ := hAcov s (Finset.mem_image_of_mem _ hsS)
      exact hv a ha (cosetSet_trans_decomp hvs' hsa)
    · intro a ha
      exact Set.indicator_of_notMem (hv a ha) _

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvariantHeisenbergWeyl
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.LawW

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.PcB

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

def qm (hn : ρ + p = n) (x : Mx D ρ p) : Mx D (n + n) (n + n) :=
  blk4 (bl hn 1 0 (adj x) 1) 0 0 (bl hn 1 (-x) 0 1)

theorem qm_mul_w (M : Maps D hn) (x : Mx D ρ p) :
    qm hn x * mat M.w = mat M.w * mat (M.nzx 0 x) := by
  rw [M.w_mat, M.nzx_mat, qm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have hz : ((0 : hermA D ρ).1 : Mx D ρ ρ) = 0 := rfl
  rw [hz]
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.neg_mul, neg_zero, neg_neg]
  congr 1
  · change _ = (Matrix.fromBlocks 0 0 (adj x) 0 + Matrix.fromBlocks 1 0 0 0).submatrix _ _
    rw [Matrix.fromBlocks_add]; simp
  · change _ = (Matrix.fromBlocks 0 (-x) 0 0 + Matrix.fromBlocks 0 0 0 1).submatrix _ _
    rw [Matrix.fromBlocks_add]; simp

theorem mat_conj (M : Maps D hn) (x : Mx D ρ p) : mat (M.w * M.nzx 0 x * M.w⁻¹) = qm hn x := by
  have h : mat M.w * mat M.w⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc mat (M.w * M.nzx 0 x * M.w⁻¹) = (mat M.w * mat (M.nzx 0 x)) * mat M.w⁻¹ := rfl
    _ = qm hn x * (mat M.w * mat M.w⁻¹) := by rw [← qm_mul_w, mul_assoc]
    _ = qm hn x := by rw [h, mul_one]

theorem exists_low (hn : ρ + p = n) (c : Mx D p ρ) :
    ∃ a : GL (Fin n) (AE D), a.1 = bl hn 1 0 c 1 :=
  ⟨⟨bl hn 1 0 c 1, bl hn 1 0 (-c) 1, by rw [lowerUnipotent_mul, add_neg_cancel, blockMatrix_one], by rw [lowerUnipotent_mul, neg_add_cancel, blockMatrix_one]⟩, rfl⟩

theorem det_low (hn : ρ + p = n) (c : Mx D p ρ) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 0 c 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  change a.1.det = 1
  rw [ha, bl, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem blkA_qm (hn : ρ + p = n) (x : Mx D ρ p) : blkA (qm hn x) = bl hn 1 0 (adj x) 1 := by
  ext i j
  simp [qm, blkA, blk4, Matrix.toBlocks₁₁]

theorem law_w : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ),
    IsLaw χ s f → ∀ (x : Mx D ρ p) (h : G D n), f (M.w * M.nzx 0 x * h) = f (M.w * h) := by
  intro D n ρ p hn M χ s f hf x h
  have hq := mat_conj M x
  have hP : M.w * M.nzx 0 x * M.w⁻¹ ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq
  obtain ⟨a, ha⟩ := exists_low hn (adj x)
  have hA : blkA (mat (M.w * M.nzx 0 x * M.w⁻¹)) = a.1 := by rw [hq, blkA_qm, ha]
  have key := hf _ hP a hA (M.w * h)
  rw [det_low hn (adj x) a ha, map_one, map_one] at key
  have e : M.w * M.nzx 0 x * M.w⁻¹ * (M.w * h) = M.w * M.nzx 0 x * h := by group
  rw [e] at key
  simpa using key

end GlobalTheory.CompanionTheory.FJE.LawW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreAction
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

open _root_.Topology

theorem range_finite {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

theorem exists_nhds_translation_invariant {A Z : Type} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [AddCommGroup Z] {φ : A → Z} (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) : ∃ N ∈ 𝓝 (0 : A), ∀ w ∈ N, ∀ v, φ (v + w) = φ v := by
  letI := IsTopologicalAddGroup.rightUniformSpace A
  haveI := isUniformAddGroup_of_addCommGroup (G := A)
  letI : UniformSpace Z := ⊥
  haveI : DiscreteTopology Z := ⟨rfl⟩
  have hu : UniformContinuous φ := hc.uniformContinuous_of_continuous hl.continuous
  have hid : {p : Z × Z | p.1 = p.2} ∈ _root_.uniformity Z := by
    have : _root_.uniformity Z = Filter.principal {p : Z × Z | p.1 = p.2} := rfl
    rw [this]
    exact Filter.mem_principal_self _
  have h1 := hu hid
  rw [Filter.mem_map, uniformity_eq_comap_nhds_zero A, Filter.mem_comap] at h1
  obtain ⟨N, hN, hsub⟩ := h1
  refine ⟨N, hN, fun w hw v => ?_⟩
  have h2 : (v, v + w) ∈ (fun x : A × A => x.2 - x.1) ⁻¹' N := by
    show v + w - v ∈ N
    simpa using hw
  exact (hsub h2).symm

theorem isOpen_stabiliser {G V : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (h : {g | ρ g v = v} ∈ 𝓝 (1 : G)) :
    IsOpen {g | ρ g v = v} :=
  _root_.UpperTheory.Reformulated.B.Yhd4.main ρ v h

theorem isSmooth_fibAct (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (hρ : IsSmooth ρ₀) :
    IsSmooth (fibAct t ρ₀) := by
  intro φ
  refine isOpen_stabiliser (fibAct t ρ₀) φ ?_
  have hU : (⋂ z ∈ Set.range φ.1, {g : Multiplicative (Fin i → k) | ρ₀ g z = z}) ∈ 𝓝 1 :=
    (Filter.biInter_mem (range_finite φ.2.1 φ.2.2)).2 fun z _ =>
      (hρ z).mem_nhds (show ρ₀ 1 z = z by rw [map_one, Module.End.one_apply])
  obtain ⟨N, hN, hinv⟩ := exists_nhds_translation_invariant φ.2.1 φ.2.2
  have hT : Continuous fun y : Multiplicative (Fin (i + t) → k) =>
      Multiplicative.ofAdd (topP i t y.toAdd) :=
    continuous_ofAdd.comp ((continuous_topP i t).comp continuous_toAdd)
  have hM : Continuous fun y : Multiplicative (Fin (i + t) → k) => middlePart i t y.toAdd :=
    (continuous_midP i t).comp continuous_toAdd
  have h1 := hT.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hU
  have h2 := hM.continuousAt (x := 1) |>.preimage_mem_nhds (t := _) hN
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro y ⟨hy1, hy2⟩
  apply Subtype.ext
  funext v
  show ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) = φ.1 v
  rw [hinv _ hy2 v]
  exact Set.mem_iInter₂.1 hy1 (φ.1 v) ⟨v, rfl⟩

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTopRepresentation
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply]
    rw [show ρ b v = v from hb]
    exact ha
  one_mem' := by
    show ρ 1 v = v
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    show ρ a⁻¹ v = v
    have ha' : ρ a v = v := ha
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem stabSub_add_le (ρ : Representation ℂ G V) (x y : V) :
    stabSub ρ x ⊓ stabSub ρ y ≤ stabSub ρ (x + y) := by
  intro g hg
  show ρ g (x + y) = x + y
  have h1 : ρ g x = x := hg.1
  have h2 : ρ g y = y := hg.2
  rw [map_add (f := _), h1, h2]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop

open GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmTop in
theorem GlobalTheory.CompanionTheory.BZPsiPG.FibKer.isSmooth_topRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V), IsSmooth τ → IsSmooth (topRep τ W) := by
  intro k _ _ _ _ i V W _ _ _ _ τ hτ v
  have hU : Continuous (uMh k i) := (_root_.GlobalTheory.CompanionTheory.BZPsiPG.continuous_levi_uM_mirProj k i).2.1.comp continuous_toAdd
  suffices h : IsOpen (stabSub (topRep τ W) v : Set (Multiplicative (Fin i → k))) from h
  induction v using TensorProduct.induction_on with
  | zero =>
    have : (stabSub (topRep τ W) 0 : Set (Multiplicative (Fin i → k))) = Set.univ := by
      ext g
      simp only [Set.mem_univ, iff_true]
      show topRep τ W g 0 = 0
      exact map_zero _
    rw [this]
    exact isOpen_univ
  | tmul a b =>
    have hle : (stabSub τ a).comap (uMh k i) ≤ stabSub (topRep τ W) (a ⊗ₜ[ℂ] b) := by
      intro g hg
      have hg' : τ (uM k i g.toAdd) a = a := hg
      show LinearMap.rTensor W (τ (uM k i g.toAdd)) (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] b
      rw [LinearMap.rTensor_tmul, hg']
    refine Subgroup.isOpen_mono hle ?_
    exact (hτ a).preimage hU
  | add x y hx hy =>
    exact Subgroup.isOpen_mono (stabSub_add_le _ x y) (by rw [Subgroup.coe_inf]; exact hx.inter hy)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFinite
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem weil_fock_mem (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) (hr : ResEta D χ V.rank) (θ : InfFam D) (hθ : IsInfFam θ)
    (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (hω : IsWeilSch ψ χ θ V μ ω)
    (l : D.what₂.Tau → ℝ) (hl : HasRealPar ψ θ l) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (Φ : schwartzA θ V.rank n) (hΦ : Φ.1 ∈ fockA θ V n l s)
    (k : G D n) (hk : k ∈ K D n) : (ω k Φ).1 ∈ fockA θ V n l s := by
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    _root_.GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := _root_.GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := _root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := _root_.GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    _root_.GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      _root_.GlobalTheory.CartanFockDeg.om_keeps_fockDeg D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := _root_.GlobalTheory.StdUnn.sch_mem_fockA D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

theorem weilKFin : WeilKFin := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  have hfin := GlobalTheory.StdUnn.KFin.fock_kfinite D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  set S := Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ} with hS
  refine ⟨S.map (schwartzA θ V.rank n).subtype, Module.Finite.map S _, ?_, ?_⟩
  · rw [hS, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, ⟨k, hk, rfl⟩, rfl⟩
    exact weil_fock_mem D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ k hk
  · intro k hk
    exact ⟨ω k Φ, Submodule.subset_span ⟨k, hk, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.ThTot

end
end

