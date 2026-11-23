module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientsEquivOfNotLe
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCore

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_quotient_of_eq {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P Q : Submodule ℂ W)
    (hP : ∀ g, P ≤ P.comap (σ g)) (hQ : ∀ g, Q ≤ Q.comap (σ g)) (h : P = Q) :
    Nonempty ((σ.quotient P hP).Equiv (σ.quotient Q hQ)) := by
  subst h
  exact ⟨Representation.Equiv.mk' (Representation.IntertwiningMap.id _) id
    (fun _ => rfl) (fun _ => rfl)⟩

theorem eq_or_eq_top_of_isIrreducible_quotient {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (P : Submodule ℂ W) (hP : ∀ g, P ≤ P.comap (σ g))
    (hirr : (σ.quotient P hP).IsIrreducible) (M : Submodule ℂ W)
    (hM : ∀ g, M ≤ M.comap (σ g)) (hPM : P ≤ M) : M = P ∨ M = ⊤ := by
  haveI : IsSimpleOrder (Subrepresentation (σ.quotient P hP)) := hirr
  let N : Subrepresentation (σ.quotient P hP) :=
    ⟨M.map P.mkQ, by
      rintro g _ ⟨m, hm, rfl⟩
      exact ⟨σ g m, hM g hm, rfl⟩⟩
  let S₀ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊥, by
      intro g v hv
      rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]⟩
  let S₁ : Subrepresentation (σ.quotient P hP) :=
    ⟨⊤, by
      intro _ _ _
      exact Submodule.mem_top⟩
  have hcomap : (M.map P.mkQ).comap P.mkQ = M := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hPM]
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · left
    have h1 : N ⊓ S₀ = N := by rw [hN, bot_inf_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_inf] at h2
    have h3 : M.map P.mkQ = ⊥ := le_bot_iff.mp (inf_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_bot, Submodule.ker_mkQ]
  · right
    have h1 : N ⊔ S₁ = N := by rw [hN, top_sup_eq]
    have h2 := congrArg Subrepresentation.toSubmodule h1
    rw [Subrepresentation.toSubmodule_sup] at h2
    have h3 : M.map P.mkQ = ⊤ := top_le_iff.mp (sup_eq_left.mp h2)
    rw [← hcomap, h3, Submodule.comap_top]

theorem nonempty_equiv_subQuot (ρ : Representation ℂ G V) (E K L : Subrepresentation ρ)
    (hK : (subQuot E K).IsIrreducible) (hL : (subQuot E L).IsIrreducible)
    (hE : ¬ E ≤ E ⊓ K ⊔ E ⊓ L) : Nonempty ((subQuot E K).Equiv (subQuot E L)) := by
  have hPK : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact K.2 g hx
  have hPL : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype).comap (E.toRepresentation g) := by
    intro g x hx
    exact L.2 g hx
  have hK' : (E.toRepresentation.quotient _ hPK).IsIrreducible := hK
  have hL' : (E.toRepresentation.quotient _ hPL).IsIrreducible := hL
  have hsup : ∀ g, K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≤
      (K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    exact sup_le ((hPK g).trans (Submodule.comap_mono le_sup_left))
      ((hPL g).trans (Submodule.comap_mono le_sup_right))
  have hsup' : ∀ g, L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≤
      (L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype).comap
        (E.toRepresentation g) := by
    intro g
    rw [sup_comm]
    exact hsup g
  have hne : K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    intro htop
    apply hE
    have hle : E.toSubmodule ≤ E.toSubmodule ⊓ K.toSubmodule ⊔ E.toSubmodule ⊓ L.toSubmodule := by
      intro x hx
      have hmem : (⟨x, hx⟩ : E.toSubmodule) ∈
          K.toSubmodule.comap E.toSubmodule.subtype ⊔ L.toSubmodule.comap E.toSubmodule.subtype := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      exact Submodule.mem_sup.mpr ⟨y, ⟨y.2, hy⟩, z, ⟨z.2, hz⟩, congrArg Subtype.val hyz⟩
    rw [← inf_eq_left]
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_sup,
      Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_inf]
    exact inf_eq_left.mpr hle
  have hne' : L.toSubmodule.comap E.toSubmodule.subtype ⊔ K.toSubmodule.comap E.toSubmodule.subtype ≠ ⊤ := by
    rw [sup_comm]
    exact hne
  have h1 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPK hK' _ hsup le_sup_left).resolve_right hne
  have h2 := (GlobalTheory.CompanionTheory.GenCore.eq_or_eq_top_of_isIrreducible_quotient _ _ hPL hL' _ hsup' le_sup_left).resolve_right hne'
  have hPQ : K.toSubmodule.comap E.toSubmodule.subtype = L.toSubmodule.comap E.toSubmodule.subtype :=
    le_antisymm (sup_eq_left.mp h2) (sup_eq_left.mp h1)
  exact GlobalTheory.CompanionTheory.GenCore.nonempty_equiv_quotient_of_eq E.toRepresentation _ _ hPK hPL hPQ

end GlobalTheory.CompanionTheory.GenCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaOfLinearReductive
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exp_mem_unitaryGroup {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1
  rw [← Matrix.exp_conjTranspose, hX]
  exact (Matrix.exp_neg X ▸ Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)))

theorem frame {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧
      U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ ∈ 𝔤 ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) * Y = Y * (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) →
        (Uᴴ * Y * U).IsDiag := by
  obtain ⟨𝔞, hle, hH, hC, hM⟩ := _root_.GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace 𝔤
  obtain ⟨U₀, hU₀, hD⟩ := GlobalTheory.T.commuting_hermitian_simultaneous_diag (𝔞 : Set (Matrix (Fin n) (Fin n) ℂ)) hH hC
  obtain ⟨H, hHa, hreg⟩ := _root_.GlobalTheory.CompanionTheory.IwaGen.exists_regular_point 𝔞 U₀
  have hU₀' : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
  have hU₀'' : U₀ᴴ * U₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hU₀
  let d : Fin n → ℝ := fun i => ((U₀ᴴ * H * U₀) i i).re
  have hdd : Matrix.diagonal (fun i => (d i : ℂ)) = U₀ᴴ * H * U₀ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have : star ((U₀ᴴ * H * U₀) i i) = (U₀ᴴ * H * U₀) i i := by
        have h2 : (U₀ᴴ * H * U₀)ᴴ = U₀ᴴ * H * U₀ := by
          simp [Matrix.conjTranspose_mul, hH H hHa, Matrix.mul_assoc]
        exact congrFun (congrFun h2 i) i
      have h3 := Complex.conj_eq_iff_real.1 this
      obtain ⟨r, hr⟩ := h3
      simp [d, hr]
    · simp [Matrix.diagonal_apply_ne _ hij, hD H hHa hij]
  have hHd : U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ = H := by
    rw [hdd]
    calc U₀ * (U₀ᴴ * H * U₀) * U₀ᴴ = (U₀ * U₀ᴴ) * H * (U₀ * U₀ᴴ) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hU₀']; simp
  obtain ⟨U, hU, h, hanti, heq, hdiag⟩ := _root_.GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder U₀ d hU₀
  refine ⟨U, hU, h, hanti, ?_, ?_⟩
  · rw [heq, hHd]; exact hle hHa
  · intro Y hY hYs hcomm
    rw [heq, hHd] at hcomm
    apply hdiag
    refine hD Y (hM Y hY hYs fun A hA => ?_)
    exact GlobalTheory.T.centralizer_regular_commutes U₀ H A Y hU₀ (hD H hHa) (hD A hA) (fun i j hij => hreg i j hij A hA) hcomm

theorem alg {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hs : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hb : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧
      (Uᴴ * B * U).BlockTriangular id := by
  obtain ⟨U, hU, h, hanti, hd, hreg⟩ := frame 𝔤
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have cj : ∀ Z : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * Z * U) * Uᴴ = Z := fun Z => by
    calc U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h1]; simp
  have cj' : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * Z * Uᴴ) * U = Z := fun Z => by
    calc Uᴴ * (U * Z * Uᴴ) * U = (Uᴴ * U) * Z * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h2]; simp
  let φ : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun Z => U * Z * Uᴴ
      map_add' := fun a b => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r a => by simp }
  let 𝔥 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤.comap φ
  have mem : ∀ Z, Z ∈ 𝔥 ↔ U * Z * Uᴴ ∈ 𝔤 := fun Z => Iff.rfl
  have mem' : ∀ Z ∈ 𝔤, Uᴴ * Z * U ∈ 𝔥 := fun Z hZ => by rw [mem, cj]; exact hZ
  have mulc : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, (U * P * Uᴴ) * (U * Q * Uᴴ) = U * (P * Q) * Uᴴ := fun P Q => by
    calc (U * P * Uᴴ) * (U * Q * Uᴴ) = U * P * (Uᴴ * U) * Q * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp [Matrix.mul_assoc]
  have hs' : ∀ Z ∈ 𝔥, Zᴴ ∈ 𝔥 := fun Z hZ => by
    have := hs _ ((mem Z).1 hZ)
    rw [mem]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  have hb' : ∀ P ∈ 𝔥, ∀ Q ∈ 𝔥, P * Q - Q * P ∈ 𝔥 := fun P hP Q hQ => by
    have := hb _ ((mem P).1 hP) _ ((mem Q).1 hQ)
    rw [mulc, mulc] at this
    rw [mem, Matrix.mul_sub, Matrix.sub_mul]
    exact this
  have hreg' : ∀ Y ∈ 𝔥, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag := by
    intro Y hY hYs hc
    have := hreg _ ((mem Y).1 hY) (by simp [Matrix.conjTranspose_mul, hYs, Matrix.mul_assoc]) (by rw [mulc, mulc, hc])
    rwa [cj'] at this
  refine ⟨U, hU, fun X hX => ?_⟩
  obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := GlobalTheory.T.exists_skewHermitian_add_blockTriangular 𝔥 h hanti (_root_.GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise 𝔥 h ((mem _).2 hd) hb') hs' hreg' _ (mem' X hX)
  refine ⟨U * A * Uᴴ, (mem _).1 hA, U * B * Uᴴ, (mem _).1 hB, ?_, ?_, ?_⟩
  · rw [← Matrix.add_mul, ← Matrix.mul_add, ← hAB, cj]
  · simp [Matrix.conjTranspose_mul, hAs, Matrix.mul_assoc]
  · rwa [cj']

theorem iwaOn_of_isLinRed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → PositivityTheory.Tls2.Iua.IwaOn G := by
  intro n G hG
  obtain ⟨𝔤, hiff, hV⟩ := _root_.GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra hG
  obtain ⟨hs, hb⟩ := _root_.GlobalTheory.CompanionTheory.LieStable.lieAlg_stable hG 𝔤 hiff
  obtain ⟨U, hU, hdec⟩ := alg 𝔤 hs hb
  have hexp : ∀ X ∈ 𝔤, NormedSpace.exp X ∈ G := fun X hX => by
    simpa using (hiff X).1 hX 1
  let 𝔨 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | Xᴴ = -X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.conjTranspose_add, ha, hb, neg_add]
      zero_mem' := by simp
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        ext i j
        have := congrFun (congrFun ha i) j
        simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
        simp [Matrix.conjTranspose_apply, this] }
  let 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | (Uᴴ * X * U).BlockTriangular id}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul]
        exact ha.add hb
      zero_mem' := by simp [Matrix.BlockTriangular]
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        intro i j hij
        have := ha hij
        have e : Uᴴ * (r • a) * U = r • (Uᴴ * a * U) := by simp
        rw [e, Matrix.smul_apply, this, smul_zero] }
  have hloc := GlobalTheory.T.local_exp_product_decomposition hG 𝔤 𝔨 𝔟 hiff hV inf_le_left inf_le_left (fun X hX => by
    obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := hdec X hX
    rw [hAB]
    exact Submodule.add_mem_sup ⟨hA, hAs⟩ ⟨hB, hBt⟩)
  obtain h := _root_.GlobalTheory.CompanionTheory.LinRedFactor.factor_of_local hG U hU (by
    filter_upwards [hloc] with g hg hgG
    obtain ⟨X, hX, Y, hY, rfl⟩ := hg hgG
    exact ⟨_, ⟨hexp X hX.1, exp_mem_unitaryGroup X hX.2⟩, _, hexp Y hY.1, rfl, GlobalTheory.T.exp_block_triangular U Y hU hY.2⟩)
  exact ⟨U, hU, h⟩

end GlobalTheory.CompanionTheory.IwaGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquivFoundationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_equiv_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), ∃ e : Jacquet π (unipRad k (stdBlocks d hd)) ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.JacquetModule k N (Zl.JC.blockIdx d hd) π, (∀ v : V, e (Submodule.Quotient.mk v) = Representation.Coinvariants.mk _ v) ∧ ∀ (g : Levi k (fun a => Fin (d a))) (hg : leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd)) (x : Jacquet π (unipRad k (stdBlocks d hd))), e (jacU (stdBlocks d hd) π g x) = GroundTheory.Automorphic.Parabolic.jacquetAction k N (Zl.JC.blockIdx d hd) π ⟨_, hg⟩ (e x) := by
  intro k _ _ _ _ N V _ _ π h d hd
  have hPQ := GlobalTheory.CompanionTheory.ParabolicCompare.unipRad_stdBlocks_eq_unipotentRadical k h N d hd
  have hK : twKer π (unipRad k (stdBlocks d hd)) 1 =
      Representation.Coinvariants.ker
        (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)).subtype) := by
    rw [hPQ]
    exact GlobalTheory.CompanionTheory.JacquetDict.twKer_one_eq_coinvariantsKer π _
  refine ⟨Submodule.quotEquivOfEq _ _ hK, ?_, ?_⟩
  · intro v
    rfl
  · intro g hg x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityDropZeroBlocks
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos Matrix

namespace GlobalTheory.CompanionTheory.FineProd.JmDrop

section Blocks

variable {R : Type} [Field R] {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem dropHom_surjective (ho : Function.Injective o) :
    Function.Surjective (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o) := by
  classical
  intro x
  have key : ∀ (j : Fin r) (b : Fin r') (hb : o b = j) (a : Fin r') (ha : o a = j),
      (hb ▸ x b : GL (Fin (d j)) R) = ha ▸ x a := by
    intro j b hb a ha
    obtain rfl : b = a := ho (hb.trans ha.symm)
    rfl
  refine ⟨(fun j => if hj : ∃ a, o a = j then hj.choose_spec ▸ x hj.choose else 1 :
    ∀ j, GL (Fin (d j)) R), ?_⟩
  funext a
  have hj : ∃ b, o b = o a := ⟨a, rfl⟩
  show (if hj : ∃ b, o b = o a then (hj.choose_spec ▸ x hj.choose : GL (Fin (d (o a))) R) else 1) = x a
  rw [dite_eq_left hj]
  exact key (o a) _ hj.choose_spec a rfl

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}

theorem unipRad_eq (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) : unipRad R e = unipRad R e' := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GlobalTheory.SmGL.mem_unipRad,
    GlobalTheory.SmGL.mem_parab_iff, GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b i j hab => ?_, fun a i j => ?_⟩
    · rw [he, he]
      exact h1 _ _ i j (hm hab)
    · rw [he, he]
      exact h2 _ i j
  · rintro ⟨h1, h2⟩
    refine ⟨fun A B i j hBA => ?_, fun A i j => ?_⟩
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      obtain ⟨b, rfl⟩ := hne B (Fin.pos j).ne'
      rw [← he, ← he]
      exact h1 a b i j (hm.lt_iff_lt.1 hBA)
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      rw [← he, ← he]
      exact h2 a i j

theorem leviEmb_eq (hm : StrictMono o) (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩)
    (g : Levi R fun j => Fin (d j)) :
    leviEmb R e g = leviEmb R e' (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective q
  by_cases hab : a = b
  · subst hab
    have h1 := GlobalTheory.SmGL.leviEmb_apply_same R e g (o a) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_same R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) a i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm
  · have h1 := GlobalTheory.SmGL.leviEmb_apply_ne R e g (hm.injective.ne hab) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_ne R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) hab i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm


omit [Fintype n] [DecidableEq n] in
theorem modExp_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    modExp (fun b => Fin (d (o b))) a = modExp (fun j => Fin (d j)) (o a) := by
  unfold GlobalTheory.SmGL.modExp
  congr 1
  all_goals
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Fintype.sum_of_injective o hm.injective _ _ (fun j hj => ?_) (fun b => ?_)
    · by_cases hd : d j = 0
      · simp [hd]
      · exact absurd (hne j hd) hj
    · simp [hm.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem deltaHalf_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g =
      deltaHalf k (fun a => Fin (d (o a))) (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) := by
  rw [GlobalTheory.SmGL.deltaHalf_apply, GlobalTheory.SmGL.deltaHalf_apply]
  symm
  refine Fintype.prod_of_injective o hm.injective _ _ (fun j hj => ?_) (fun a => ?_)
  · have hd : d j = 0 := by
      by_contra hd
      exact hj (hne j hd)
    haveI : IsEmpty (Fin (d j)) := by
      rw [hd]
      infer_instance
    have hdet : Matrix.GeneralLinearGroup.det (g j) = 1 := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
    rw [hdet, map_one]
  · rw [GlobalTheory.CompanionTheory.FineProd.JmDrop.modExp_drop hm hne a]
    first
    | rfl
    | skip

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def jacDrop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) (π : Representation ℂ (GL n k) V) :
    (GlobalTheory.SmGL.jac e π).Equiv
      ((GlobalTheory.SmGL.jac e' π).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) :=
  have h3 : twKer π (unipRad k e) 1 = twKer π (unipRad k e') 1 := by rw [unipRad_eq hm hne he]
  .mk (Submodule.quotEquivOfEq _ _ h3) fun g => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.quotEquivOfEq _ _ h3 (GlobalTheory.SmGL.jac e π g (Submodule.Quotient.mk v)) =
      GlobalTheory.SmGL.jac e' π (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) (Submodule.Quotient.mk v)
    rw [jac_mk, jac_mk, map_smul, deltaHalf_drop hm hne, leviEmb_eq hm he]
    rfl

end Local

theorem jm_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  intro k _ _ _ _ r r' N y hd o hm hne hd' V _ _ π
  have he := _root_.GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty (fun j => (y j).1) hd o hm hne hd'
  obtain ⟨φ⟩ := GlobalTheory.T.tensor_product_drop_zero_factors y o hm hne
  unfold Zc.jm
  rw [GlobalTheory.SmGL.jhMult_congr_left φ,
    GlobalTheory.SmGL.jhMult_congr_right _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.jacDrop (d := fun j => (y j).1) (o := o) hm hne he π),
    GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.dropHom_surjective (R := k) (d := fun j => (y j).1) hm.injective)]

end GlobalTheory.CompanionTheory.FineProd.JmDrop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionFixedSurjective
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem mk_mem_fixed_jac : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈ fixed (GlobalTheory.SmGL.jac (stdBlocks d hd) π) (KM k N J d hd) := by
  intro k _ _ _ _ N h d hd J _ hc _ _ V _ _ π _ v x
  have hx : leviEmb k (stdBlocks d hd) (x : Levi k (Bl d)) ∈ J := x.2
  have hv : π (leviEmb k (stdBlocks d hd) (x : Levi k (Bl d))) (v : V) = (v : V) := by
    simpa using v.2 ⟨_, hx⟩
  have hδ : deltaHalf k (Bl d) (x : Levi k (Bl d)) = 1 := _root_.GlobalTheory.CompanionTheory.HalfModCompact.deltaHalf_eq_one_of_mem_KM k N h d hd J hc x x.2
  rw [jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmoothStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_restriction_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ), F ∈ Sm E (r + s) → (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | exact GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice1.sm_lev_slice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinusStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_psi_minus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.SmPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus | exact GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMirFun.smPsiMinus <;> assumption)
end

