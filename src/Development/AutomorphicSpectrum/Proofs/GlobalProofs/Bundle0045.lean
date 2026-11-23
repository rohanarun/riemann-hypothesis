module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult
open GlobalTheory.DiagCell

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem cell_diag {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (b : SizeMatrix m m) (hrz : ∀ i j, j ≠ i → b.1 i j = 0)
    (ρ : Representation ℂ (Levi k m) W) (hsm : IsSmooth ρ) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  have hcz : ∀ j i, i ≠ j → b.1 i j = 0 := fun j i hi => hrz i j (Ne.symm hi)
  have hcard : ∀ i, Fintype.card (Fin (b.1 i i)) = Fintype.card (m i) := by
    intro i
    have r := b.2.1 i
    rw [Finset.sum_eq_single i (fun j _ hj => hrz i j hj) (by simp)] at r
    simpa using r
  let E : ∀ i, Fin (b.1 i i) ≃ m i := fun i => Fintype.equivOfCardEq (hcard i)
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ m i := fun i =>
    (OneBlockCell.valEquiv (n := fun j => b.1 i j) i rfl (fun j hj => hrz i j hj)).trans (E i)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ m j := fun j =>
    (OneBlockCell.valEquiv (n := fun i => b.1 i j) j rfl (fun i hi => hcz j i hi)).trans (E j)
  refine ⟨f, g, ?_⟩
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k m) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) i (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      OneBlockCell.deltaHalf_eq_one_of_single i (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      OneBlockCell.deltaHalf_eq_one_of_single j (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) j (fun i hi => hcz j i hi) (x j)
  have hfg : ∀ i (t : Fin (b.1 i i)), f i ⟨i, t⟩ = g i ⟨i, t⟩ := fun i t => rfl
  have hγ : ∀ (p : relParab k g),
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) =
        (p : Levi k m) := by
    intro p
    funext i
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f i).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f i).surjective y
    have ha : a = i := by
      by_contra hne
      have h1 := hrz i a hne
      have h2 := t.2
      omega
    have ha' : a' = i := by
      by_contra hne
      have h1 := hrz i a' hne
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same, hfg, hfg]
    rfl
  let Ψ : W ≃ₗ[ℂ] Jacquet ρ (relUnip k f) := (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk u := fun u => rfl
  let τ := (twist ((relJac f ρ).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ (ρ p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ, hγ p]
    simp only [inv_one, Units.val_one, one_smul]
  let F : ρ.IntertwiningMap (cellFunctor f g ρ) :=
    { toFun := fun u => ⟨⟨fun x => Ψ (ρ x u), fun p x => by
          show Ψ (ρ (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : ρ x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (ρ (y * x) u) = Ψ (ρ y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (ρ x (ρ h u)) = Ψ (ρ (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (ρ 1 u) = Ψ (ρ 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (ρ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem isSubquotient_comp_mulSingle {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hi : ∀ a, (ρ a).IsIrreducible) (c : α) :
    IsSubquotient (ρ c) ((piTensor ρ).comp (MonoidHom.mulSingle Γ c) :
      Representation ℂ (Γ c) (PiTensorProduct ℂ fun a => X a)) := by
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (hi a)
  obtain ⟨Z, _, _, υ, hυ, hs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
    ((piTensor ρ).comp (MonoidHom.mulSingle Γ c)) hn
  obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient hυ (hi c) (isSubquotient_factor ρ c hυ hs)
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans hs

theorem exists_of_cell (h' : CellSemisimplification k) {α β : Type} [Fintype α] [LinearOrder α] [Fintype β]
    [LinearOrder β] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β → Type}
    [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {b : α → β → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ m i) (g : ∀ j, (Σ i, Fin (b i j)) ≃ m' j)
    {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)} (hρ : ∀ i, IsSmooth (ρ i)) (hl : ∀ i, HasFiniteLength (ρ i))
    {τ : Representation ℂ (Levi k m') Y} (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (h0 : jhMult τ (cellFunctor f g (piTensor ρ)) ≠ 0) :
    ∃ s : ∀ i j, IrrRep (GL (Fin (b i j)) k),
      (∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (GlobalTheory.SmGL.jac (f i) (ρ i))) ∧
        IsSubquotient τ (piTensor fun j => multiProd (g j) fun i => (s i j).ρ) := by
  obtain ⟨T, -, hT⟩ := h' α β m m' _ f g X ρ hρ hl
  rw [hT ⟨Y, τ, hτs, hτ⟩] at h0
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  exact ⟨fun i j => (s i j).rep, fun i => jhMult_ne_zero_iff.1
    (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i)),
    jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)⟩

theorem offdiag_eq_zero (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL (k := k))} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) {b : Fin 2 → Fin 2 → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (d j))
    {τ : Representation ℂ (Levi k fun i => Fin (d i)) Y} (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (y : ∀ i, IrrRep (GL (Fin (d i)) k))
    (hy : ∀ i, IsSubquotient (y i).ρ (τ.comp (MonoidHom.mulSingle (fun i => GL (Fin (d i)) k) i) :
      Representation ℂ (GL (Fin (d i)) k) Y))
    (hys : ∀ i, HasSupport (y i).ρ (A i))
    (h0 : jhMult τ (cellFunctor f g (piTensor fun i => (p i).π)) ≠ 0) : b 0 1 = 0 ∧ b 1 0 = 0 := by
  obtain ⟨s, hrow, hcol⟩ := exists_of_cell (hG k).2 f g (fun i => (p i).smooth)
    (fun i => hasFiniteLength_of_isIrreducible (p i).irr) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin 2 → Multiset (IrrGL (k := k)), (∀ j, HasSupport (s i j).ρ (t j)) ∧ A i = ∑ j, t j :=
    fun i => exists_sum_of_jac hG hBZ (hA i) (f i) (_root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).ρ (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b i j = d j := by simpa using Fintype.card_congr (g j)
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  have hU : ∀ j, A j = ∑ i, t i j := fun j => hasSupport_unique hG hBZ (hys j) (hC j)
  simp only [Fin.sum_univ_two] at hAt hU
  have e1 : t 0 1 = t 1 0 := add_left_cancel ((hAt 0).symm.trans (hU 0))
  have hw : t 0 1 = 0 := Multiset.eq_zero_of_forall_notMem fun x hx =>
    hAB x (hAt 0 ▸ Multiset.mem_add.2 (Or.inr hx)) (hAt 1 ▸ Multiset.mem_add.2 (Or.inl (e1 ▸ hx)))
  have hd1 := (ht 0 1).sum_fst
  have hd2 := (ht 1 0).sum_fst
  rw [← e1, hw] at hd2
  rw [hw] at hd1
  simp only [Multiset.map_zero, Multiset.sum_zero, Fintype.card_fin] at hd1 hd2
  exact ⟨hd1.symm, hd2.symm⟩

theorem jhMult_jac_multiProd (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL (k := k))} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) {N : ℕ} (e e' : (Σ i, Fin (d i)) ≃ Fin N)
    {τ : Representation ℂ (Levi k fun i => Fin (d i)) Y} (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (y : ∀ i, IrrRep (GL (Fin (d i)) k))
    (hy : ∀ i, IsSubquotient (y i).ρ (τ.comp (MonoidHom.mulSingle (fun i => GL (Fin (d i)) k) i) :
      Representation ℂ (GL (Fin (d i)) k) Y))
    (hys : ∀ i, HasSupport (y i).ρ (A i)) :
    jhMult τ (GlobalTheory.SmGL.jac e' (multiProd e fun i => (p i).π)) = jhMult τ (piTensor fun i => (p i).π) := by
  classical
  let M := fun i : Fin 2 => Fin (d i)
  haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _
  let b₀ : SizeMatrix M M := ⟨fun i j => if i = j then d i else 0, by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp [M]
    · simp [M]⟩
  have hρ : IsSmooth (piTensor fun i => (p i).π) := isSmooth_piTensor fun i => (p i).smooth
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ
  let f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b =>
    if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j := fun b =>
    if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some
  have hf : f b₀ = f₀ := by simp [f]
  have hg : g b₀ = g₀ := by simp [g]
  have h1 := (hG k).1.jhMult_eq (m := M) (m' := M) e e' hρ f g hτ
  refine (show jhMult τ (GlobalTheory.SmGL.jac e' (multiProd e fun i => (p i).π)) = _ from h1).trans ?_
  rw [Finset.sum_eq_single b₀]
  · have key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ →
        jhMult τ (cellFunctor f' g' (piTensor fun i => (p i).π)) = jhMult τ (piTensor fun i => (p i).π) := by
      rintro _ _ rfl rfl
      exact jhMult_congr_right τ E₀
    exact key _ _ hf hg
  · intro b _ hb
    by_contra hne
    obtain ⟨z1, z2⟩ := offdiag_eq_zero hG hBZ p hA hAB (f b) (g b) hτ hτs y hy hys hne
    refine hb (Subtype.ext (funext fun i => funext fun j => ?_))
    have r0 := b.2.1 0
    have r1 := b.2.1 1
    simp only [Fin.sum_univ_two, M, Fintype.card_fin] at r0 r1
    fin_cases i <;> fin_cases j <;> simp_all [b₀]
  · simp

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemUnipOfArchFrame
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.GoodPos

open GlobalTheory.StdPar GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {r : ℕ}

theorem pow_support (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
    (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) (k : ℕ) :
    ∀ i j, (Q ^ (k + 1)) i j ≠ 0 → P i j ∧ i.val + k + 1 ≤ j.val := by
  induction k with
  | zero =>
    intro i j h
    rw [zero_add, pow_one] at h
    have := hQ i j h
    exact ⟨this, by have := hPlt i j this; rw [Fin.lt_def] at this; omega⟩
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih i l (left_ne_zero_of_mul hl)
    have h2 := hQ l j (right_ne_zero_of_mul hl)
    refine ⟨hPt i l j h1.1 h2, ?_⟩
    have := hPlt l j h2
    rw [Fin.lt_def] at this
    omega

theorem exists_inv_pattern (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
    (Q : Matrix (Fin r) (Fin r) A) (hQ : ∀ i l, Q i l ≠ 0 → P i l) :
    ∃ Q' : Matrix (Fin r) (Fin r) A, (∀ i l, Q' i l ≠ 0 → P i l) ∧ (1 + Q) * (1 + Q') = 1 := by
  have hQn : ∀ i l, (-Q) i l ≠ 0 → P i l := fun i l h => hQ i l (by simpa using h)
  have hnil : (-Q) ^ (r + 1) = 0 := by
    ext i j
    by_contra h
    have := (pow_support P hPt hPlt (-Q) hQn r i j h).2
    have := j.2
    omega
  refine ⟨∑ t ∈ Finset.range r, (-Q) ^ (t + 1), fun i l h => ?_, ?_⟩
  · rw [Matrix.sum_apply] at h
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (pow_support P hPt hPlt (-Q) hQn t i l ht).1
  · have e := mul_neg_geom_sum (-Q) (r + 1)
    rw [hnil, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix _ _ _)] at e
    exact e

end Lin

section Main

theorem mem_unip_of_arch_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (Xf : Matrix (Fin n) (Fin r) E)
    (S : Finset (Fin r)) (u : GAd σ J), u ∈ infPts σ J →
    (∀ w : InfinitePlace F, ∃ N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E),
      (matHom _ σ J (projArch σ J w u)).1 * Xf.map (inclR (F := F) w.Completion) =
        Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
      (∀ i j, N i j ≠ 0 → ∃ k ∈ S, i ≤ k ∧ k < j) ∧
      (∀ v : Fin n → w.Completion ⊗[F] E,
        (∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ v) i = 0) →
        ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → ∃ k ∈ S, i ≤ k) ∧
          (matHom _ σ J (projArch σ J w u)).1 *ᵥ v - v = Xf.map (inclR (F := F) w.Completion) *ᵥ a)) →
    u ∈ GlobalTheory.StdPar.unip σ J Xf S := by
  intro F E _ _ _ _ _ σ n J r Xf S u hu hN
  classical
  choose Nw hM hQw hPw using hN
  let ψ : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  let N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := Matrix.of fun i v => glueInf F E (fun w => Nw w i v)
  have hcN : ∀ w, N.map (compInf F E w) = Nw w := fun w => Matrix.ext fun i v => compInf_glueInf _ w
  have hsN : N.map ψ = 0 := Matrix.ext fun i v => sndA_glueInf _
  have hcZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E) (w : InfinitePlace F),
      (adMat F Z).map (compInf F E w) = Z.map (inclR (F := F) w.Completion) := fun Z w =>
    Matrix.ext fun i j => by
      show compInf F E w ((1 : AF F) ⊗ₜ[F] Z i j) = (1 : w.Completion) ⊗ₜ[F] Z i j
      simp [compInf]
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u).1 with hMdef
  have hcM : ∀ w, M.map (compInf F E w) = (matHom _ σ J (projArch σ J w u)).1 := fun w =>
    Matrix.ext fun a b => by rw [matHom_projArch]; rfl
  have hsM : M.map ψ = 1 := Matrix.ext fun a b =>
    congrArg (fun g => (g : GL (Fin n) _).1 a b) hu
  set C := adMat F Xf with hC
  have hMat : M * C = C + C * N := by
    ext a b
    apply tens_ext
    · intro w
      have e1 : compInf F E w ((M * C) a b) = ((M * C).map (compInf F E w)) a b := rfl
      have e2 : compInf F E w ((C + C * N) a b) = ((C + C * N).map (compInf F E w)) a b := rfl
      rw [e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hcM, hcN, hC, hcZ, hM w]
    · show ψ _ = ψ _
      have e1 : ψ ((M * C) a b) = ((M * C).map ψ) a b := rfl
      have e2 : ψ ((C + C * N) a b) = ((C + C * N).map ψ) a b := rfl
      rw [e1, e2, Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hsM, hsN, Matrix.one_mul,
        Matrix.mul_zero, add_zero]
  let P : Fin r → Fin r → Prop := fun i j => ∃ k ∈ S, i ≤ k ∧ k < j
  have hPt : ∀ i l j, P i l → P l j → P i j := fun i l j ⟨k, hk, h1, h2⟩ ⟨k', hk', h1', h2'⟩ =>
    ⟨k', hk', h1.trans (h2.le.trans h1'), h2'⟩
  have hPlt : ∀ i l, P i l → i < l := fun i l ⟨k, _, h1, h2⟩ => lt_of_le_of_lt h1 h2
  have hQ : ∀ i l, N i l ≠ 0 → P i l := by
    intro i l h
    by_contra hc
    apply h
    have : (fun w => Nw w i l) = fun _ => 0 := funext fun w => by
      by_contra h'
      exact hc (hQw w i l h')
    show glueInf F E _ = 0
    rw [this, glueInf_zero]
  obtain ⟨N', hQ', hinv⟩ := exists_inv_pattern P hPt hPlt N hQ
  set M' : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J u⁻¹).1 with hM'def
  have hM'M : M' * M = 1 := by
    rw [hM'def, hMdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hMC : M * C = C * (1 + N) := by rw [hMat, Matrix.mul_add, Matrix.mul_one]
  have hM'C : M' * C = C * (1 + N') := by
    calc M' * C = M' * (C * ((1 + N) * (1 + N'))) := by rw [hinv, Matrix.mul_one]
      _ = M' * (M * C) * (1 + N') := by rw [hMC]; simp only [Matrix.mul_assoc]
      _ = C * (1 + N') := by rw [← Matrix.mul_assoc, hM'M, Matrix.one_mul]
  have hsupp : ∀ (D : Set (Fin r)) (Q : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)), (∀ i l, Q i l ≠ 0 → P i l) →
      (∀ i l, P i l → l ∈ D → i ∈ D) → ∀ a : Fin r → AF F ⊗[F] E, (∀ l, l ∉ D → a l = 0) →
      ∀ l, l ∉ D → ((1 + Q) *ᵥ a) l = 0 := by
    intro D Q hq hD a ha i hi
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, ha i hi, zero_add]
    show ∑ l, Q i l * a l = 0
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : Q i l = 0
    · rw [h, zero_mul]
    · rw [ha l (fun hl => hi (hD i l (hq i l h) hl)), mul_zero]
  have hstab : ∀ D : Set (Fin r), (∀ i l, P i l → l ∈ D → i ∈ D) →
      ∀ y, y ∈ colSpan F Xf D ↔ M *ᵥ y ∈ colSpan F Xf D := by
    intro D hD y
    constructor
    · intro hy
      obtain ⟨a, ha, rfl⟩ := (mem_span_cols_iff C D y).1 hy
      refine (mem_span_cols_iff C D _).2 ⟨(1 + N) *ᵥ a, hsupp D N hQ hD a ha, ?_⟩
      rw [mulVec_mulVec, mulVec_mulVec, hMC]
    · intro hy
      obtain ⟨a, ha, hay⟩ := (mem_span_cols_iff C D _).1 hy
      refine (mem_span_cols_iff C D _).2 ⟨(1 + N') *ᵥ a, hsupp D N' hQ' hD a ha, ?_⟩
      rw [mulVec_mulVec, ← hM'C, ← mulVec_mulVec, hay, mulVec_mulVec, hM'M, one_mulVec]
  refine ⟨Subgroup.mem_iInf.2 fun j => ⟨fun y => hstab _ (fun i l h hl => hPt i l j h hl) y, fun y hy => ?_⟩,
    hstab _ (fun i l ⟨k, hk, h1, _⟩ _ => ⟨k, hk, h1⟩), fun y hy => ?_⟩
  · rw [colSpan, Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    show M *ᵥ _ - _ ∈ _
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ _ ((mem_span_cols_iff C _ _).2 ⟨fun i => N i j, fun l hl => ?_, ?_⟩)
    · by_contra h
      exact hl (hQ l j h)
    · have e : M *ᵥ Cᵀ j = fun i => (M * C) i j := by
        funext i
        simp [mulVec, dotProduct]
        rfl
      rw [e, hMat]
      funext i
      show (C *ᵥ fun i => N i j) i = (C + C * N) i j - C i j
      rw [Matrix.add_apply, add_sub_cancel_left]
      rfl
  · have hy' : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → (adMat F (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ y) i = 0 := fun i hi =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy i) hi
    have hyw : ∀ w : InfinitePlace F, ∀ i : Fin r, (∃ k ∈ S, i ≤ k) →
        ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion) *ᵥ (compInf F E w ∘ y)) i = 0 := by
      intro w i hi
      have := congrArg (compInf F E w) (hy' i hi)
      rwa [RingHom.map_mulVec, hcZ, map_zero] at this
    choose a ha hA using fun w => hPw w (compInf F E w ∘ y) (hyw w)
    let A : Fin r → AF F ⊗[F] E := fun i => glueInf F E (fun w => a w i)
    have hcA : ∀ w, compInf F E w ∘ A = a w := fun w => funext fun i => compInf_glueInf _ w
    have hsA : ψ ∘ A = 0 := funext fun i => sndA_glueInf _
    refine (mem_span_cols_iff C _ _).2 ⟨A, fun l hl => ?_, ?_⟩
    · have : (fun w => a w l) = fun _ => 0 := funext fun w => by
        by_contra h'
        exact hl (ha w l h')
      show glueInf F E _ = 0
      rw [this, glueInf_zero]
    · funext i
      apply tens_ext
      · intro w
        have e1 : compInf F E w ((M *ᵥ y - y) i) =
            ((matHom _ σ J (projArch σ J w u)).1 *ᵥ (compInf F E w ∘ y) - compInf F E w ∘ y) i := by
          rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, hcM]
          rfl
        rw [e1, congrFun (hA w) i, RingHom.map_mulVec, hC, hcZ, hcA]
      · show ψ _ = ψ _
        rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hsM, one_mulVec, hsA, mulVec_zero]
        simp

end Main

end GlobalTheory.CompanionTheory.GoodPos
end
end

