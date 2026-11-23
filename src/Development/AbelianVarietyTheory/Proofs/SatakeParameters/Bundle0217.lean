module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0203

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SwapTwo

open GlobalTheory.JacTensor GlobalTheory.EmptyFirstBlock

theorem nonempty_equiv_of_apply_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) {v : V} (hv : f v ≠ 0) : Nonempty (ρ.Equiv σ) := by
  let K : Subrepresentation ρ := ⟨LinearMap.ker f.toLinearMap, fun g x hx => by
    show f (ρ g x) = 0
    rw [f.isIntertwining]
    have hx' : f x = 0 := hx
    rw [hx', map_zero]⟩
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨ρ g x, f.isIntertwining _ _ g x⟩⟩
  refine ⟨GlobalTheory.LocGL.equivOfBijective f ⟨?_, ?_⟩⟩
  · rcases eq_bot_or_eq_top K with h | h
    · refine (injective_iff_map_eq_zero f.toLinearMap).2 fun x hx => ?_
      have : x ∈ K := hx
      rw [h] at this
      exact this
    · exact absurd (show v ∈ K from h ▸ trivial) hv
  · rcases eq_bot_or_eq_top R with h | h
    · exact absurd (show f v ∈ R from ⟨v, rfl⟩) (by rw [h]; exact hv)
    · intro w
      obtain ⟨x, hx⟩ := (show w ∈ R from h ▸ trivial)
      exact ⟨x, hx⟩

theorem exists_jac_map_ne_zero : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)),
    (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n),
    ∃ (φ : (GlobalTheory.SmGL.jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')), φ x ≠ 0 := by
  intro _ hGL k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  obtain ⟨z, c, c', hz, hcc, hX, hbad⟩ := _root_.GlobalTheory.CellCentral.exists_central_scalar_ne_cell k d σ hσ hd1 hnt
  obtain ⟨N, b, hb⟩ := (hGL k).1 (Fin 2) (Fin 2) n (fun i => Fin (d i)) (fun j => Fin (d (Equiv.swap 0 1 j))) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))),
      G0.1 = ![![0, d 0], ![1, 0]] := ⟨⟨![![0, d 0], ![1, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two, hd1]
      · fin_cases j <;> simp [Fin.sum_univ_two, hd1]⟩, rfl⟩
  have hgood : (b (b.symm G0)).1 1 0 = 1 := by rw [Equiv.apply_symm_apply, hG0]; rfl
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := _root_.GlobalTheory.OneBlockCell.cellFunctor_swap_equiv k d σ hd1 (b (b.symm G0)) hgood
  have hbad' : ∀ t, t ≠ b.symm G0 → (b t).1 1 0 = 0 := by
    intro t ht
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r1 c0 r0 c1
    by_contra hne
    apply ht
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    funext i j
    rw [hG0]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  have hstep : ∀ t, t ≠ b.symm G0 → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y := by
    intro t ht y
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    apply E.toLinearEquiv.injective
    have h1 : E.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) z y) = _ := LinearMap.congr_fun (E.isIntertwining' z) y
    have h2 := hbad (b t) (hbad' t ht) (b t).nonempty_rows.some (b t).nonempty_cols.some (E.toLinearEquiv y)
    exact h1.trans (h2.trans (LinearEquiv.map_smul E.toLinearEquiv c' y).symm)
  obtain ⟨φ, v, hv⟩ := _root_.GlobalTheory.exists_intertwining_of_central_step (GlobalTheory.SmGL.jac e' (multiProd e fun i => (σ i).π))
    (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) N S hmono h0 hN z hz (b.symm G0) c (fun _ => c')
    (fun _ _ => hcc.symm) hstep
    ⟨(h4 (b.symm G0) f₀ g₀).some.trans E₀⟩ hX
    (GlobalTheory.ProdSupport.nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr)
  exact ⟨φ, v, hv⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_of_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (φ : G →* H) (h : Representation.IsIrreducible (ρ.comp φ)) :
    ρ.IsIrreducible := by
  haveI : Nontrivial V := Model.nontrivial_of_isIrreducible h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact hv h1
  · rcases eq_bot_or_eq_top (⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩ :
        Subrepresentation (ρ.comp φ)) with h' | h'
    · left
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2
    · right
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2

theorem not_equiv_twist_symm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (π₁ : Irr k r) (π₂ : Irr k t),
    (∀ (h : r = t) (α : ℂˣ), ¬ Nonempty ((h ▸ π₁ : Irr k t).π.Equiv (twist π₂.π (detChar (Fin t) (unrChar k α))))) →
    ∀ (h : t = r) (α : ℂˣ), ¬ Nonempty ((h ▸ π₂ : Irr k r).π.Equiv (twist π₁.π (detChar (Fin r) (unrChar k α)))) := by
  intro k _ _ _ _ r t π₁ π₂ hnt h α ⟨φ⟩
  subst h
  refine hnt rfl α⁻¹ ?_
  have heq : twist (twist π₁.π (detChar (Fin t) (unrChar k α))) (detChar (Fin t) (unrChar k α⁻¹)) = π₁.π := by
    ext g v
    simp only [twist_apply, detChar_apply, unrChar_apply, smul_smul, inv_zpow]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have e := (GlobalTheory.LocGL.twistEquiv φ (detChar (Fin t) (unrChar k α⁻¹))).symm
  rw [heq] at e
  exact ⟨e⟩

theorem isIrreducible_multiProd_two (hU : GlobalTheory.Published.UnlinkedProductIrreducible) {n : Type} [Fintype n]
    [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)) (hσ : ∀ i, 0 < d i ∧ IsCuspidal (σ i).π)
    (hnt : ∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α)))))
    (e : (Σ i, Fin (d i)) ≃ n) : (multiProd e fun i => (σ i).π).IsIrreducible := by
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  have hsupp : ∀ i, IsCuspSupport (σ i).π (fun _ : Fin 1 => d i) (fun _ => (σ i).π) := fun i => by
    obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (σ i).smooth (oneBlock (d i)) fun _ _ => rfl
    exact ⟨(σ i).irr, fun _ => ⟨(hσ i).1, (σ i).irr, (hσ i).2⟩, oneBlock (d i),
      .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩
  have h2 := hU k (d 0) (d 1) 1 1 (σ 0) (σ 1) _ _ _ _ (hsupp 0) (hsupp 1) fun _ _ h α => hnt h α
  obtain ⟨E₁⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (σ i).π
  have h3 := GlobalTheory.Parabolic.isIrreducible_of_equiv E₁ h2
  have hc : Fintype.card (Fin (d 0 + d 1)) = Fintype.card n := by
    rw [Fintype.card_fin, ← hd, ← Fintype.card_congr e]; simp
  let ψ : Fin (d 0 + d 1) ≃ n := Fintype.equivOfCardEq hc
  obtain ⟨E₂⟩ := GlobalTheory.T.normalisedParabolicInduction_reindex_equiv k (Fin 2) (fun i => Fin (d i)) _ _ (stdBlocks d hd) ψ _ (piTensor fun i => (σ i).π)
  have h4 := isIrreducible_of_comp _ (GlobalTheory.Parabolic.isIrreducible_of_equiv E₂ h3)
  obtain ⟨E₃⟩ := (Placing.parInd_jac_placing k (Fin 2) n (fun i => Fin (d i)) ((stdBlocks d hd).trans ψ) e _).1
    (piTensor fun i => (σ i).π)
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E₃ h4

theorem swap_two_equiv : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 → (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) → ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n), Nonempty ((multiProd e fun i => (σ i).π).Equiv (multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π)) := by
  intro hBZ hGL hU k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  have h1 := isIrreducible_multiProd_two hU d σ hσ hnt e
  have h2 := isIrreducible_multiProd_two hU (fun i => d (Equiv.swap 0 1 i)) (fun i => σ (Equiv.swap 0 1 i))
    (fun i => hσ _) (not_equiv_twist_symm k (d 0) (d 1) (σ 0) (σ 1) hnt) e'
  obtain ⟨φ, x, hx⟩ := exists_jac_map_ne_zero hBZ hGL k n d σ hσ hd1 hnt e e'
  obtain ⟨f, hf⟩ := (Model.evalOne_bijective e' (isSmooth_parInd _ _)
    (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)).2 φ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : f v ≠ 0 := fun h => hx (by
    rw [← hf]
    show (f v).1.1 1 = 0
    rw [h]; rfl)
  exact nonempty_equiv_of_apply_ne_zero h1 h2 f hv

end GlobalTheory.SwapTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Back

theorem exists_level_vec_in_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → (R.toCx3 F).PartsW false → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  obtain ⟨w, hw, hw0, hws⟩ := _root_.GlobalTheory.Hk3.exists_part_level_vector R F hCW hEx hSch s hOk hGG hLU j c h0
  exact ⟨w, hw, hw0, _root_.GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS R F hParts j w hws⟩

theorem blockProd_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (P : B.Pl) : B.blockProd P ≠ 0 := by
  unfold BlockDat.blockProd
  rw [ne_eq, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  intro ν _ h
  unfold Formalism.L2.Col.blockPoly at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨c, _, hc⟩ := h
  have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hc
  simp at this

theorem eig_in_sum {H : Type} [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H] {Q J K : Type} (ok : Q → Prop)
    (h : Q → J → Module.End ℂ H) (ev : K → Q → J → ℂ) (V : K → Submodule ℂ H) (S : K → Prop) (k0 : K)
    (hc : ∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c'))
    (hev : ∀ k P, ok P → ∀ cc, ∀ x ∈ V k, h P cc x = ev k P cc • x)
    (w : H) (hw : w ∈ V k0) (hw0 : w ≠ 0) (hwS : w ∈ ⨆ (k : K) (_ : S k), V k) :
    ∃ k, S k ∧ ∀ P, ok P → ∀ cc, ev k P cc = ev k0 P cc := by
  classical
  let op : {P // ok P} × J → Module.End ℂ H := fun i => h i.1.1 i.2
  have hpc : Formalism.L2.Col.PairComm op := fun i i' => hc _ _ i.1.2 i'.1.2 _ _
  let χ : K → {P // ok P} × J → ℂ := fun k i => ev k i.1.1 i.2
  have hV : ∀ k, V k ≤ Formalism.L2.Col.eigAt op (χ k) := fun k x hx =>
    Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hev k i.1.1 i.1.2 i.2 x hx
  by_contra hne
  push_neg at hne
  have h1 : (⨆ (k : K) (_ : S k), V k) ≤ Formalism.L2.Col.eigSum op (fun x => x ≠ χ k0) := by
    refine iSup₂_le fun k hk => (hV k).trans (Formalism.L2.Col.eigAt_le_eigSum ?_)
    intro he
    obtain ⟨P, hP, cc, hcc⟩ := hne k hk
    exact hcc (congrFun he (⟨P, hP⟩, cc))
  have h2 : V k0 ≤ Formalism.L2.Col.eigSum op (fun x => x = χ k0) :=
    (hV k0).trans (Formalism.L2.Col.eigAt_le_eigSum rfl)
  have hd := Formalism.L2.Col.disjoint_eigSum (op := op) hpc (C := fun x => x = χ k0) (C' := fun x => x ≠ χ k0)
    (fun x h h' => h' h)
  exact hw0 ((Submodule.disjoint_def.1 hd) w (h2 hw) (h1 hwS))

theorem types_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (hSep : A3.fam3.TypesSep3) (j : Fin D.R.m)
    (p p' : A3.fam3.base3.Ix) (y : (A3.liftI j A3.A.μ0).OpIx → ℂ)
    (hp : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) y)
    (hp' : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p'.1)) y) : p = p' := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨x', hx', hxx⟩ := hp'
  have hxe : x = x' := funext fun i => D.what₂.embLL.injective (congrFun hxx i)
  subst hxe
  by_contra hne
  have hne' : p.1 ≠ p'.1 := fun h => hne (Subtype.ext h)
  rcases hSep p.1 p.2 p'.1 p'.2 hne' j with ⟨P, hP⟩ | ⟨k, hk⟩
  · apply hP
    have h1 := hx.1 P
    have h2 := hx'.1 P
    rw [h1] at h2
    exact mul_right_cancel₀ (blockProd_ne_zero _ P) h2
  · exact hk ((hx.2 k).symm.trans (hx'.2 k))

theorem wc_le_wp_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr hParts hSep j pl cV cW hLD p c hsys
  obtain ⟨hcoreF, hSF, -, -, -, hWeq, -⟩ := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hCW
  have hcore := hcoreF hEx
  obtain ⟨h, -, hNorm, -, hsum, -, hev, hchar⟩ :=
    _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hcore hSch hOk.ok2.irr R.SF hSF j
  have hidem := (eH_laws R.toRealDat F.lv2 hcore hOk.ok2.irr j).1
  by_cases h0 : R.Wc' j c = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨w, hwc, hw0, hwp⟩ := exists_level_vec_in_parts R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  have hwp' : w ∈ ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
    have hle : (⨆ p, R.Wp3 j p) ≤
        ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
      refine iSup_le fun p' => iSup₂_le fun c' hc' => ?_
      rw [hWeq]
      exact le_iSup₂_of_le (f := fun c' (_ : ∃ p', R.Carries p' c') => Wcc R.toRealDat R.SF j c') c' ⟨p', hc'⟩ le_rfl
    exact hle hwp
  rw [hWeq] at hwc
  obtain ⟨c', ⟨p', hcar⟩, hag⟩ := eig_in_sum (Good R.toRealDat A3.A.μ0) h
    (fun c P cc => evC (Wc D j) P (c P) cc) (Wcc R.toRealDat R.SF j) (fun c' => ∃ p', R.Carries p' c') c hNorm.1
    (fun k P hP cc x hx => hev k P hP cc x hx) w hwc hw0 hwp'
  have hsub : Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro x hx
    refine hchar c' x ?_ ?_
    · have hr : x ∈ LinearMap.range (eH R.toRealDat j) := hsum ▸ (le_iSup (Wcc R.toRealDat R.SF j) c hx)
      obtain ⟨y, rfl⟩ := hr
      rw [← Module.End.mul_apply, hidem]
    · intro P d hP hd
      rw [hev c P hP _ x hx, ← hag P hP]
      simp [evC, hd]
  have hne : R.Wc' j c' ≠ ⊥ := by
    rw [hWeq]
    intro hb
    exact hw0 ((Submodule.eq_bot_iff _).1 hb w (hsub hwc))
  have hfwd := _root_.GlobalTheory.Hk3.passage_of_carried hHowe R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr j pl cV cW hLD p' c' hcar hne
  have hlab : labW j pl cW c' = labW j pl cW c := funext fun i => hag (pl i) (hLD.good i) (cW i)
  rw [hlab] at hfwd
  have hpp : p' = p := types_eq hSep j p' p _ hfwd hsys
  subst hpp
  rw [hWeq]
  refine hsub.trans ?_
  rw [← hWeq]
  exact le_iSup₂_of_le (f := fun c (_ : R.Carries p' c) => R.Wc' j c) c' hcar le_rfl

end GlobalTheory.Hk3.Back
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSpherical
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

noncomputable section

namespace GlobalTheory.SatExists

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivOutside_mul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

theorem trivOutside_inv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hNf⟩ := π.irrS.1.le hf₀S
  let U : Subgroup (GAf L n) :=
    Subgroup.closure ({κ | NG.Cong L n N κ} ∪ {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ})
  have hUmax : U ≤ Umax L n := (Subgroup.closure_le _).2 (by
    rintro κ (hκ | hκ)
    · exact hκ.1
    · exact hκ.1)
  have hUv : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) := fun κ hκ =>
    ⟨fun h => hUmax h, fun h => Subgroup.subset_closure (Or.inr ⟨h, hκ⟩)⟩
  have hCU : ∀ κ, NG.Cong L n N κ → κ ∈ U := fun κ hκ => Subgroup.subset_closure (Or.inl hκ)
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := by
    intro κ hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact funext fun g => hNf x hx g
      · exact hf₀K x hx.1 hx.2
    | one => exact funext fun g => by change f₀ (g * 1) = f₀ g; rw [mul_one]
    | mul x y _ _ hx hy =>
      refine funext fun g => ?_
      change f₀ (g * (x * y)) = f₀ g
      have h1 : f₀ (g * x * y) = f₀ (g * x) := congrFun hy (g * x)
      have h2 : f₀ (g * x) = f₀ g := congrFun hx g
      rw [← mul_assoc, h1, h2]
    | inv x _ hx =>
      refine funext fun g => ?_
      change f₀ (g * x⁻¹) = f₀ g
      have h1 : f₀ (g * x⁻¹ * x) = f₀ (g * x⁻¹) := congrFun hx (g * x⁻¹)
      rw [← h1, inv_mul_cancel_right]
  have hdec : ∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨a, b, e, ha, hat, hb, hc⟩ := GlobalTheory.T.congruence_element_decompose L n v N x hx
        exact ⟨a, b, e, (hUv a hat).2 ha, hat, hCU b hb, hc⟩
      · exact ⟨x, 1, (mul_one x).symm, Subgroup.subset_closure (Or.inr hx), hx.2, one_mem _,
          fun y _ => by rw [mul_one, one_mul]⟩
    | one => exact ⟨1, 1, (mul_one 1).symm, one_mem _, trivOutside_one v, one_mem _,
        fun y _ => by rw [mul_one, one_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      obtain ⟨a', b', rfl, ha', hat', hb', hbc'⟩ := hy
      refine ⟨a * a', b * b', ?_, mul_mem ha ha', trivOutside_mul hat hat', mul_mem hb hb', fun z hz => ?_⟩
      · simp only [mul_assoc]
        rw [← mul_assoc b a', ← hbc a' hat', mul_assoc]
      · rw [← mul_assoc, hbc z hz, mul_assoc, hbc' z hz, ← mul_assoc]
    | inv x _ hx =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      refine ⟨a⁻¹, b⁻¹, ?_, inv_mem ha, trivOutside_inv hat, inv_mem hb, fun z hz => ?_⟩
      · rw [mul_inv_rev, eq_mul_inv_iff_mul_eq, mul_assoc, hbc a⁻¹ (trivOutside_inv hat), inv_mul_cancel_left]
      · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hbc z hz, inv_mul_cancel_left]
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      add_mem' := fun ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add (f := _), ha.2 κ hκ, hb.2 κ hκ]⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI : FiniteDimensional ℂ V := by
    have := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (_root_.GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n) hN
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) ?_
    rintro f ⟨hfS, hfU⟩
    exact ⟨(π.irrS.1.le hfS).1, fun κ hκ g => congrFun (hfU κ (hCU κ hκ)) g⟩
  have hf₀V : f₀ ∈ V := ⟨hf₀S, hf₀U⟩
  haveI : Nontrivial V := ⟨⟨⟨f₀, hf₀V⟩, 0, fun e => hf₀0 (congrArg Subtype.val e)⟩⟩
  let T : Hecke ℂ (KU Dv.σw n) → Module.End ℂ V := fun h =>
    { toFun := fun f => ⟨heckeFunI L n U Dv h.1 f.1,
        _root_.GlobalTheory.HeckeStab.heckeFunI_mem L n v w Dv U hUv π.W π.S π.irrS.1.stable h.1 h.2 f.1 f.2.1,
        _root_.GlobalTheory.heckeFunI_rt_invariant L n v w Dv U hUv hdec π.W h.1 h.2 f.1 f.2.2⟩
      map_add' := fun f f' => Subtype.ext ((_root_.GlobalTheory.InertHeckeLin.heckeFunI_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 1 f.1 f'.1).2.2.1)
      map_smul' := fun c f => Subtype.ext ((_root_.GlobalTheory.InertHeckeLin.heckeFunI_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.2.2) }
  have hT : ∀ h (f : V), ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h.1 f.1 := fun _ _ => rfl
  have hcomm : ∀ a b, T a * T b = T b * T a := fun a b => LinearMap.ext fun f => Subtype.ext (by
    change heckeFunI L n U Dv a.1 (heckeFunI L n U Dv b.1 f.1) = heckeFunI L n U Dv b.1 (heckeFunI L n U Dv a.1 f.1)
    rw [← _root_.GlobalTheory.InertConv.heckeFunI_conv L n v w Dv U hUv π.W a.1 a.2 b.1 b.2 f.1 f.2.2,
      ← _root_.GlobalTheory.InertConv.heckeFunI_conv L n v w Dv U hUv π.W b.1 b.2 a.1 a.2 f.1 f.2.2,
      GlobalTheory.UnitarySwap.heckeCommU _ Dv.ϖ Dv.σw _ n ℂ Dv.unram a.1 a.2 b.1 b.2])
  obtain ⟨f, hf0, hμ⟩ := GlobalTheory.exists_common_eigenvector_of_commute T hcomm
  choose μ hμ using hμ
  have ev : ∀ h : Hecke ℂ (KU Dv.σw n), heckeFunI L n U Dv h.1 f.1 = μ h • f.1 := fun h =>
    congrArg Subtype.val (hμ h)
  have hf'0 : (f : GAf L n → π.W) ≠ 0 := fun e => hf0 (Subtype.ext e)
  have inj := smul_left_injective ℂ hf'0
  let l : Hecke ℂ (KU Dv.σw n) →ₗ[ℂ] ℂ :=
    { toFun := μ
      map_add' := fun h h' => inj (by
        change μ (h + h') • f.1 = (μ h + μ h') • f.1
        rw [← ev, add_smul, ← ev, ← ev]
        exact (_root_.GlobalTheory.InertHeckeLin.heckeFunI_bilinear L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 1 f.1 f.1).1)
      map_smul' := fun c h => inj (by
        change μ (c • h) • f.1 = (c * μ h) • f.1
        rw [← ev, mul_smul, ← ev]
        exact (_root_.GlobalTheory.InertHeckeLin.heckeFunI_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.1) }
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq Dv.unram l
    (inj (by
      change μ _ • f.1 = (1 : ℂ) • f.1
      rw [← ev, one_smul]
      exact _root_.GlobalTheory.OneAct.heckeFunI_unit L n v w Dv U hUv π.W f.1 f.2.2))
    (fun h h' => inj (by
      change μ _ • f.1 = (μ h * μ h') • f.1
      rw [← ev]
      change heckeFunI L n U Dv (conv (KU Dv.σw n) h.1 h'.1) f.1 = _
      rw [_root_.GlobalTheory.InertConv.heckeFunI_conv L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 f.1 f.2.2, ev h',
        (_root_.GlobalTheory.InertHeckeLin.heckeFunI_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 (μ h') f.1 f.1).2.2.2, ev h, smul_smul, mul_comm]))
  refine ⟨fun i => (α i : ℂ), f.1, f.2.1, hf'0, U, f.2.2, hUv, fun h hh => ?_⟩
  rw [ev ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.SatExists
end
end

