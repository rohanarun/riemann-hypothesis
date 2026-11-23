module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnipotentSubgroupFiniteGeneration
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenExact

theorem mem_span_openFns_of_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (Q : Subgroup (GL (Fin N) k)), Q ≤ unipB k (Fin N) → (∀ s : Finset (GL (Fin N) k), (↑s : Set (GL (Fin N) k)) ⊆ Q → ∃ L : Subgroup (GL (Fin N) k), L ≤ Q ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧ IsCompact (L : Set (GL (Fin N) k))) → ∀ θ : Q →* ℂˣ, (∀ (q : Q) (hq : (q : GL (Fin N) k) ∈ unipB k (Fin N)), θ q = whitChar ψ N ⟨q, hq⟩) → ∀ f ∈ openFns d hd ρ, f ∈ twKer (parInd (stdBlocks d hd) ρ) Q θ → f ∈ Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ, x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g} := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ Q hQ hex θ hθ f hf hker
  let σ : Representation ℂ Q (IndSp (stdBlocks d hd) ρ) := (parInd (stdBlocks d hd) ρ).comp Q.subtype
  have hI : ∀ t : Q, ∀ v ∈ openFns d hd ρ, σ t v ∈ openFns d hd ρ := by
    intro t v hv g hg
    have h1 : v.1.1 (g * (t : GL (Fin N) k)) ≠ 0 := hg
    obtain ⟨p, hp, n, hn, e⟩ := hv _ h1
    show ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k (wOpen d hd) * n
    refine ⟨p, hp, n * (t : GL (Fin N) k)⁻¹, mul_mem hn (inv_mem (hQ t.2)), ?_⟩
    rw [← mul_assoc, ← e]
    group
  have hσs : IsSmooth σ := fun v => (isSmooth_parInd (stdBlocks d hd) ρ v).preimage continuous_subtype_val
  let ρ' : Representation ℂ Q (openFns d hd ρ) := GlobalTheory.PRep.sub σ (openFns d hd ρ) hI
  have hρs : IsSmooth ρ' := by
    intro v
    have : {t : Q | ρ' t v = v} = {t : Q | σ t (v : IndSp (stdBlocks d hd) ρ) = v} := by
      ext t
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hσs _
  let θ' : (⊤ : Subgroup Q) →* ℂˣ := θ.comp (⊤ : Subgroup Q).subtype
  have hopen : IsOpen (θ'.ker : Set (⊤ : Subgroup Q)) := by
    have hw : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) :=
      GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
    let j : (⊤ : Subgroup Q) → unipB k (Fin N) := fun x => ⟨x.1.1, hQ x.1.2⟩
    have hj : Continuous j :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    have hset : (θ'.ker : Set (⊤ : Subgroup Q)) = j ⁻¹' ((whitChar ψ N).ker : Set (unipB k (Fin N))) := by
      ext x
      show θ x.1 = 1 ↔ whitChar ψ N (j x) = 1
      rw [hθ x.1 (hQ x.1.2)]
    rw [hset]
    exact hw.preimage hj
  have hexh : ∀ s : Finset Q, (↑s : Set Q) ⊆ (⊤ : Subgroup Q) →
      ∃ L : Subgroup Q, L ≤ ⊤ ∧ (↑s : Set Q) ⊆ L ∧ IsCompact (L : Set Q) := by
    classical
    intro s _
    obtain ⟨L, hLQ, hsL, hLc⟩ := hex (s.image Subtype.val) (by
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2)
    refine ⟨L.subgroupOf Q, le_top, ?_, ?_⟩
    · intro x hx
      refine Subgroup.mem_subgroupOf.2 (hsL ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    · rw [Subtype.isCompact_iff]
      have himg : ((↑) : Q → GL (Fin N) k) '' (L.subgroupOf Q : Set Q) = (L : Set (GL (Fin N) k)) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.1 hy
        · intro hx
          exact ⟨⟨x, hLQ hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [himg]
      exact hLc
  have hle : twKer (parInd (stdBlocks d hd) ρ) Q θ ≤ twKer σ ⊤ θ' :=
    Submodule.span_le.2 (by
      rintro w ⟨q, v, rfl⟩
      exact Submodule.subset_span ⟨⟨q, trivial⟩, v, rfl⟩)
  have key : (⟨f, hf⟩ : openFns d hd ρ) ∈ twKer ρ' ⊤ θ' :=
    GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρ' σ hρs hσs ⊤ θ' hopen hexh (openFns d hd ρ).subtype
      (Submodule.injective_subtype _) (fun _ _ => rfl) ⟨f, hf⟩ (hle hker)
  have hle2 : twKer ρ' ⊤ θ' ≤ (Submodule.span ℂ {x | ∃ (q : Q), ∃ g ∈ openFns d hd ρ,
      x = parInd (stdBlocks d hd) ρ q g - (θ q : ℂ) • g}).comap (openFns d hd ρ).subtype :=
    Submodule.span_le.2 (by
      rintro _ ⟨q, g, rfl⟩
      exact Submodule.subset_span ⟨q.1, g.1, g.2, rfl⟩)
  exact hle2 key

end GlobalTheory.CompanionTheory.Rodier.OpenExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupOpenCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

open GlobalTheory.SplitWeil _root_.Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def nearSet (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {A | NearOne s A}

def ballMat (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {B | ∀ a b, B a b ∈ cball s}

theorem ballMat_eq (s : kˣ) (m : ℕ) : ballMat (k := k) s m =
    (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s : Set (Fin m → Fin m → k)) :=
  Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩

theorem isOpen_ballMat (s : kˣ) (m : ℕ) : IsOpen (ballMat (k := k) s m) := by
  simp only [ballMat, Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_cball s).preimage (f := fun A : Matrix (Fin m) (Fin m) k => A i j) (by fun_prop)

theorem isCompact_ballMat (s : kˣ) (m : ℕ) : IsCompact (ballMat (k := k) s m) := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s :
      Set (Fin m → Fin m → k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s
  rw [ballMat_eq]; exact h

theorem nearSet_eq (s : kˣ) (m : ℕ) : nearSet (k := k) s m =
    (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)) ⁻¹' ballMat s m := by
  ext A
  simp only [nearSet, NearOne, ballMat, Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.subRight_apply,
    Matrix.sub_apply]

theorem isOpen_nearSet (s : kˣ) (m : ℕ) : IsOpen (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (isOpen_ballMat s m).preimage (Homeomorph.continuous _)

theorem isCompact_nearSet (s : kˣ) (m : ℕ) : IsCompact (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)).isCompact_preimage.2 (isCompact_ballMat s m)

theorem congGL_eq (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    (congGL k s hs m : Set (GL (Fin m) k)) =
      (fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m ∩
        (fun g : GL (Fin m) k => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m :=
  rfl

theorem isOpen_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsOpen (congGL k s hs m : Set (GL (Fin m) k)) := by
  rw [congGL_eq]
  exact ((isOpen_nearSet s m).preimage Units.continuous_val).inter
    ((isOpen_nearSet s m).preimage Units.continuous_coe_inv)

theorem isCompact_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsCompact (congGL k s hs m : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK := isCompact_nearSet (k := k) s m
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin m) (Fin m) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [congGL_eq, Set.mem_inter_iff, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem congM_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
  IsOpen (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) := by
  intro k _ _ _ _ n s hs
  have e : (congM k s hs n : Set (Mir k n)) =
      (Subtype.val : Mir k n → GL (Fin (n + 1)) k) ⁻¹' (congGL k s hs (n + 1) : Set (GL (Fin (n + 1)) k)) := rfl
  rw [e]
  exact ⟨(Topo.isOpen_congGL s hs (n + 1)).preimage continuous_subtype_val,
    (GlobalTheory.CompanionTheory.BZMirOnto.isClosed_Mir k n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (Topo.isCompact_congGL s hs (n + 1))⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupsBasisNhds
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem exists_entry_nhds {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] (m : ℕ)
    {t : Set (Matrix (Fin m) (Fin m) k)} (ht : t ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) k)) :
    ∃ U ∈ 𝓝 (0 : k), ∀ A : Matrix (Fin m) (Fin m) k,
      (∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ U) → A ∈ t := by
  have hc : Continuous fun B : Matrix (Fin m) (Fin m) k => 1 + B := continuous_const.add continuous_id
  have hs : (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) k) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using ht
  have e : 𝓝 (0 : Fin m → Fin m → k) = Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := nhds_pi
  have hs' : ((fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t : Set (Fin m → Fin m → k)) ∈
      Filter.pi fun a => 𝓝 ((0 : Fin m → Fin m → k) a) := by
    rw [← e]
    exact hs
  obtain ⟨I, -, t₁, ht₁, hsub⟩ := Filter.mem_pi.1 hs'
  have h2 : ∀ a, ∃ t₂ : Fin m → Set k, (∀ b, t₂ b ∈ 𝓝 (0 : k)) ∧ Set.univ.pi t₂ ⊆ t₁ a := by
    intro a
    have e' : 𝓝 (0 : Fin m → k) = Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := nhds_pi
    have h : t₁ a ∈ Filter.pi fun b => 𝓝 ((0 : Fin m → k) b) := by
      rw [← e']
      exact ht₁ a
    obtain ⟨J, -, t₂, ht₂, hJ⟩ := Filter.mem_pi.1 h
    exact ⟨t₂, ht₂, fun x hx => hJ fun b _ => hx b (Set.mem_univ b)⟩
  choose t₂ ht₂ hsub₂ using h2
  refine ⟨⋂ a, ⋂ b, t₂ a b, Filter.iInter_mem.2 fun a => Filter.iInter_mem.2 fun b => ht₂ a b,
    fun A hA => ?_⟩
  have hmem : A - 1 ∈ (fun B : Matrix (Fin m) (Fin m) k => 1 + B) ⁻¹' t :=
    hsub fun a _ => hsub₂ a fun b _ => Set.mem_iInter.1 (Set.mem_iInter.1 (hA a b) a) b
  simpa using hmem

theorem congM_subset_nhds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ s₀ : kˣ, ∀ (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
      ValuativeRel.valuation k (s : k) ≤ ValuativeRel.valuation k (s₀ : k) →
        (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ⊆ O := by
  obtain ⟨u, hu, huO⟩ :=
    (mem_nhds_subtype ((GlobalTheory.BZMir.Mir k n : Set (GL (Fin (n + 1)) k))) 1 O).1 hO
  have hu1 : u ∈ 𝓝 (1 : GL (Fin (n + 1)) k) := by simpa using hu
  rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap, Filter.mem_comap] at hu1
  obtain ⟨w, hw, hwu⟩ := hu1
  rw [Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff] at hw
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hw
  have ht₁' : t₁ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by simpa using ht₁
  have ht₂' : MulOpposite.op ⁻¹' t₂ ∈ 𝓝 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have h := MulOpposite.continuous_op.continuousAt.preimage_mem_nhds ht₂
    simpa using h
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₁'
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.CompanionTheory.BZPhiPG.Onto.exists_entry_nhds (n + 1) ht₂'
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.SplitWeil.exists_cball_subset (Filter.inter_mem hU₁ hU₂)
  refine ⟨s₀, fun s hs hss₀ g hg => ?_⟩
  have hball : ∀ x : k, x ∈ GlobalTheory.SplitWeil.cball s → x ∈ GlobalTheory.SplitWeil.cball s₀ := by
    intro x hx
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx ⊢
    exact le_trans hx hss₀
  refine huO (hwu (hsub (Set.mem_prod.2 ⟨?_, ?_⟩)))
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.1
    show ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₁
    exact h₁ _ fun a b => (hs₀ (hball _ (hg' a b))).1
  · have hg' : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s
        (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      hg.2
    show MulOpposite.op (((g : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈ t₂
    exact h₂ _ fun a b => (hs₀ (hball _ (hg' a b))).2

end GlobalTheory.CompanionTheory.BZPhiPG.Onto
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRowM
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Chart

open GlobalTheory.CompanionTheory.BZPhiPG.Cells

section Alg

variable {k : Type} [Field k]

def rowM {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : Matrix ι ι k :=
  ((1 : Matrix ι ι k).updateRow c ρ).submatrix (Equiv.swap c j) id

theorem rowM_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowM ρ c j).det ≠ 0 := by
  have hT : ((1 : Matrix ι ι k).updateRow c ρ).det = ρ c := by
    have h := Matrix.cramer_transpose_apply (1 : Matrix ι ι k) ρ c
    rw [Matrix.transpose_one, Matrix.cramer_one] at h
    simpa using h.symm
  have h := Matrix.det_permute (Equiv.swap c j) ((1 : Matrix ι ι k).updateRow c ρ)
  have h2 : (rowM ρ c j).det = _ := h
  rw [h2, hT]
  refine mul_ne_zero ?_ hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap c j)) with e | e <;> simp [e]

theorem rowM_row {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : rowM ρ c j j = ρ := by
  ext x
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j j) x = ρ x
  simp

theorem rowM_zero {ι : Type} [DecidableEq ι] (s : ι → Prop) (ρ : ι → k) (c j : ι) (hc : s c) (hj : s j)
    (r x : ι) (hr : ¬ s r) (hx : s x) : rowM ρ c j r x = 0 := by
  have hrc : r ≠ c := fun e => hr (e ▸ hc)
  have hrj : r ≠ j := fun e => hr (e ▸ hj)
  have hrx : r ≠ x := fun e => hr (e ▸ hx)
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j r) x = 0
  rw [Equiv.swap_apply_of_ne_of_ne hrc hrj, Matrix.updateRow_ne hrc, Matrix.one_apply_ne hrx]


open Classical in
def rowB {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) : GL ι k :=
  if h : (rowM ρ c j).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem rowB_val {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowB ρ c j).val = rowM ρ c j := by
  rw [rowB, dif_pos (rowM_det_ne ρ c j hc)]
  rfl

end Alg

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]

theorem continuousOn_GL {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] (f : X → GL ι k) (V : Set X)
    (hf : ContinuousOn (fun x => (f x).val) V) : ContinuousOn f V := by
  rw [continuousOn_iff_continuous_restrict] at hf ⊢
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have hdet : Continuous fun x : V => ((f x).val).det := hf.matrix_det
  have hne : ∀ x : V, ((f x).val).det ≠ 0 := fun x => (Matrix.GeneralLinearGroup.det (f x)).ne_zero
  have e : (fun x : V => (((f x)⁻¹ : GL ι k)).val) = fun x : V => (((f x).val).det)⁻¹ • ((f x).val).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x : V => (((f x)⁻¹ : GL ι k)).val)
  rw [e]
  exact (hdet.inv₀ hne).smul hf.matrix_adjugate

theorem continuousOn_rowM {X ι : Type} [TopologicalSpace X] [DecidableEq ι] (ρ : X → ι → k) (c j : ι)
    (hρ : Continuous ρ) : Continuous fun x => rowM (ρ x) c j := by
  refine continuous_matrix fun a b => ?_
  show Continuous fun x => ((1 : Matrix ι ι k).updateRow c (ρ x)) (Equiv.swap c j a) b
  by_cases h : Equiv.swap c j a = c
  · simp only [h, Matrix.updateRow_self]
    exact (continuous_apply b).comp hρ
  · simp only [Matrix.updateRow_ne h]
    exact continuous_const

end Top

section Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem core' (i t : ℕ) (p : Mir k ((i + 1) + t + 1)) (X B : GL (Fin ((i + 1) + t + 1)) k) (j : Fin ((i + 1) + t + 1))
    (hX : X.val j = eLast k ((i + 1) + t))
    (hBj : B.val j = (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t)))
    (hB : ∀ r x : Fin ((i + 1) + t + 1), ¬ r.val < i + 1 → x.val < i + 1 → B.val r x = 0) :
    ∃ hM : (X⁻¹ * B * mirabolicProjection k _ p) ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k),
      p = h * dEmb k i t d * levi k _ X * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
  set g : GL (Fin ((i + 1) + t + 1)) k := mirabolicProjection k _ p with hg
  have hginv : mirabolicProjection k _ p⁻¹ = g⁻¹ := map_inv _ _
  rw [hginv] at hBj
  have hM : (X⁻¹ * B * g) ∈ Mir k ((i + 1) + t) := by
    have h1 : (g⁻¹ * (B⁻¹ * X)) ∈ Mir k ((i + 1) + t) := by
      rw [mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, ← hBj, ← Matrix.mul_apply_eq_vecMul, ← Units.val_mul,
        mul_inv_cancel_left, hX]
    have h2 := (Mir k ((i + 1) + t)).inv_mem h1
    simpa [mul_assoc] using h2
  let v : Fin ((i + 1) + (t + 1)) → k := fun r =>
    (p : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc r) (Fin.last _)
  let v' : Fin ((i + 1) + (t + 1)) → k := B.val.mulVec v
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append (fun x => v' (Fin.castAdd (t + 1) x)) (0 : Fin (t + 1) → k)
  let d : Fin (t + 1) → k := fun x => v' (Fin.natAdd (i + 1) x)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  have hsum : a + b = v' := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b]
    | right x => simp [a, b, d]
  let ua : Mir k ((i + 1) + t + 1) := ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd a), MirU_le_Mir k _ ⟨_, rfl⟩⟩
  have hua : ua ∈ HPG k (i + 1) (t + 1) := by
    refine mem_HPG_of (I := i + 1) (T := t + 1) ua ?_ ?_
    · intro x y
      refine unip_castSucc_castSucc _ a _ _ ?_
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    · intro x
      refine (unip_apply_castSucc_last k _ _ _).trans ?_
      show a (Fin.natAdd (i + 1) x) = 0
      simp [a]
  have hlB : levi k _ B⁻¹ ∈ HPG k (i + 1) (t + 1) := by
    have : levi k _ B ∈ HPG k (i + 1) (t + 1) := by
      refine mem_HPG_of (I := i + 1) (T := t + 1) _ ?_ ?_
      · intro x y
        refine (glEmb_castSucc_castSucc _ B _ _).trans ?_
        exact hB _ _ (by simp; omega) (by simp; omega)
      · intro x
        exact glEmb_castSucc_last _ B _
    rw [map_inv]
    exact (HPG k (i + 1) (t + 1)).inv_mem this
  refine ⟨hM, levi k _ B⁻¹ * ua, (HPG k (i + 1) (t + 1)).mul_mem hlB hua, d, ?_⟩
  apply Subtype.ext
  have hp : (p : GL (Fin ((i + 1) + t + 1 + 1)) k) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ g := eq_unip_glEmb p
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e2 : glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * glEmb k _ B := glEmb_mul_unip' k _ B _
  have e3 : glEmb k _ X * glEmb k _ (X⁻¹ * B * g) = glEmb k _ B * glEmb k _ g := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  show (p : GL (Fin ((i + 1) + t + 1 + 1)) k) = glEmb k _ B⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) *
      glEmb k _ X * glEmb k _ (X⁻¹ * B * g)
  calc (p : GL (Fin ((i + 1) + t + 1 + 1)) k)
      = (glEmb k _ B)⁻¹ * (glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v)) * glEmb k _ g := by
        rw [hp]; group
    _ = (glEmb k _ B)⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * (glEmb k _ B * glEmb k _ g) := by
        rw [e2]; simp only [mul_assoc]
    _ = _ := by
        rw [← e3, ← e1, map_inv]; simp only [mul_assoc]

end Group

theorem chart :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
      (p₀ : Mir k ((i + 1) + t + 1)), p₀ ∉ Cl k i t →
  ∃ V ∈ nhds p₀, ∃ μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t), ContinuousOn μ V ∧
    ∀ p ∈ V, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (μ p) := by
  classical
  intro k _ _ _ _ i t p₀ h₀
  have hp' : ¬ _ := fun h => h₀ ((Cl_iff i t p₀).2 h)
  push_neg at hp'
  obtain ⟨c, hcs, hc⟩ := hp'
  have hj : (piPerm i t (Fin.last ((i + 1) + t))).val < i + 1 := by rw [piPerm_last_val]; omega
  set j := piPerm i t (Fin.last ((i + 1) + t)) with hjdef
  let ρ : Mir k ((i + 1) + t + 1) → Fin ((i + 1) + t + 1) → k := fun p =>
    (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t))
  have hG : Continuous fun p : Mir k ((i + 1) + t + 1) => mirabolicProjection k _ p :=
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _
  have hρ : Continuous ρ := by
    have hv : Continuous fun p : Mir k ((i + 1) + t + 1) =>
        ((mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) :=
      Units.continuous_val.comp (hG.comp continuous_inv)
    exact continuous_pi fun x => hv.matrix_elem _ _
  let V : Set (Mir k ((i + 1) + t + 1)) := {p | ρ p c ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun ((continuous_apply c).comp hρ) continuous_const
  let W : Mir k ((i + 1) + t + 1) → GL (Fin ((i + 1) + t + 1)) k := fun p =>
    (wGL k i t)⁻¹ * rowB (ρ p) c j * mirabolicProjection k _ p
  let μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t) := fun p =>
    if h : W p ∈ Mir k ((i + 1) + t) then ⟨W p, h⟩ else 1
  have key : ∀ p ∈ V, ∃ hM : W p ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * levi k _ (wGL k i t) * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
    intro p hp
    refine core' i t p (wGL k i t) (rowB (ρ p) c j) j (wGL_row i t) ?_ ?_
    · rw [rowB_val _ _ _ hp, rowM_row]
    · intro r x hr hx
      rw [rowB_val _ _ _ hp]
      exact rowM_zero (fun x : Fin ((i + 1) + t + 1) => x.val < i + 1) _ c j hcs hj r x hr hx
  refine ⟨V, hV.mem_nhds hc, μ, ?_, ?_⟩
  · have hB : ContinuousOn (fun p => rowB (ρ p) c j) V := by
      refine continuousOn_GL _ _ ?_
      refine (continuousOn_rowM ρ c j hρ).continuousOn.congr ?_
      intro p hp
      exact rowB_val _ _ _ hp
    have hW : ContinuousOn W V :=
      (continuousOn_const.mul hB).mul hG.continuousOn
    refine (Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff).2 ?_
    refine hW.congr ?_
    intro p hp
    obtain ⟨hM, -⟩ := key p hp
    show ((μ p : Mir k ((i + 1) + t)) : GL _ k) = W p
    simp only [μ, dif_pos hM]
  · intro p hp
    obtain ⟨hM, h, hh, d, e⟩ := key p hp
    refine ⟨h, hh, d, ?_⟩
    have hμ : μ p = ⟨W p, hM⟩ := dif_pos hM
    rw [hμ]
    exact e

end GlobalTheory.CompanionTheory.BZPhiPG.Chart

end
end

