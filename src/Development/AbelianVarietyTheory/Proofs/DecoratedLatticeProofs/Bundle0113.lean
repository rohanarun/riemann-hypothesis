module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.VacMove

variable {D : D7}

theorem mt_mul_inv' (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mem_ideal_mul_mul {m n k l : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D))
    (u : Matrix (Fin n) (Fin k) (AE D)) (B : Matrix (Fin k) (Fin l) (AE D)) (hu : ∀ i j, u i j ∈ I) :
    ∀ i j, (A * u * B) i j ∈ I := by
  intro i j
  simp only [Matrix.mul_apply]
  exact I.sum_mem fun x _ => I.mul_mem_right _ (I.sum_mem fun y _ => I.mul_mem_left _ (hu y x))

theorem mem_ideal_mulVec {m n : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D)
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

def pull {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) u) (Formalism.L2.Theta.mt S g)

theorem smul_latV_mem (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a : D.host.E) (ha : a ∈ D.host.AA) :
    ∀ y ∈ GlobalTheory.FinPl.latV S L P, ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ GlobalTheory.FinPl.latA S L P := by
  intro y hy
  have key : GlobalTheory.FinPl.latV S L P ≤ (GlobalTheory.FinPl.latA S L P).comap
      (DistribSMul.toAddMonoidHom (Fin S.rank → AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D)) := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    show _ ∈ GlobalTheory.FinPl.latMul S {a | a ∈ D.host.AA} L P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact key hy

theorem mulVec_latA_mem (T : HSp D) (LT MT : Lat T) (P : Pl D → Prop) (h : GA D T) (hMT : IsSelfDualC T MT)
    (hmov : Moves T h LT MT P) : ∀ z ∈ GlobalTheory.FinPl.latA T MT P, Formalism.L2.Theta.mt T h⁻¹ *ᵥ z ∈ GlobalTheory.FinPl.latA T LT P := by
  intro z hz
  have key : GlobalTheory.FinPl.latA T MT P ≤ (GlobalTheory.FinPl.latA T LT P).comap (Matrix.mulVecLin (Formalism.L2.Theta.mt T h⁻¹)).toAddMonoidHom := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    set y' : Fin T.rank → AE D := fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] ((1 : D.host.E) * x i) with hy'def
    have hy' : y' ∈ GlobalTheory.FinPl.latV T MT P := AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, x, hx, rfl⟩
    have hent : ∀ i, y' i ∈ idAt D P := (((_root_.GlobalTheory.FinPl.localComponents D P).2 T).2.2.2 MT y' hMT.1).1 hy' |>.1
    have hy'' : Formalism.L2.Theta.mt T h⁻¹ *ᵥ y' ∈ GlobalTheory.FinPl.latV T LT P := by
      rw [hmov _ (mem_ideal_mulVec _ _ _ hent), Matrix.mulVec_mulVec, mt_mul_inv', Matrix.one_mulVec]
      exact hy'
    have hgen : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y' := by
      funext i; simp [y', Algebra.TensorProduct.tmul_mul_tmul]
    show Formalism.L2.Theta.mt T h⁻¹ *ᵥ _ ∈ GlobalTheory.FinPl.latMul T {a | a ∈ D.host.AA} LT P
    rw [hgen, Matrix.mulVec_smul]
    exact smul_latV_mem T LT P a ha _ hy''
  exact key hz

theorem vac_of_moves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P f hf g h MS MT hMS hMT hmS hmT
  unfold Vac IsLatVac at hf ⊢
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hmem : ∀ u ∈ latO S T (MS : Set _) (MT : Set _) P,
      pull g h u ∈ latO S T (LS : Set _) (LT : Set _) P := by
    intro u hu
    have hu' := (_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D S T MS MT hMS hMT P u).1 hu
    refine (_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hLS hLT P _).2 ⟨?_, ?_⟩
    · exact mem_ideal_mul_mul (idAt D P) _ _ _ hu'.1
    · intro y hy
      have hent := ((((_root_.GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 LS y hLS.1).1 hy).1
      have h1 : Formalism.L2.Theta.mt S g *ᵥ y ∈ GlobalTheory.FinPl.latV S MS P := (hmS y hent).1 hy
      have h2 := hu'.2 _ h1
      have h3 := mulVec_latA_mem T LT MT P h hMT hmT _ h2
      show (pull g h u) *ᵥ y ∈ _
      unfold pull
      rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hact : ∀ u : WO S T, actO S T g h (pull g h u) = u := by
    intro u
    unfold actO pull
    simp only [← Matrix.mul_assoc, mt_mul_inv', Matrix.one_mul]
    simp only [Matrix.mul_assoc, mt_mul_inv', Matrix.mul_one]
  have hhalf : ∀ e (u : WO S T), IsHalf e u → IsHalf e (pull g h u) := by
    intro e u hu i j
    unfold pull
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    linear_combination (Formalism.L2.Theta.mt T h⁻¹ i y * Formalism.L2.Theta.mt S g x j) * hu y x
  refine ⟨hW.om_pres (g, h) f hf1, ?_, ?_⟩
  · intro u hu
    have hw := hf2 _ (hmem u hu)
    have e1 := hW.om_heis g h (2 • (pull g h u)) f hf1
    have e2 : actO S T g h (2 • (pull g h u)) = 2 • u := by
      have := hact u
      unfold actO at this ⊢
      rw [two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul, this]
    rw [hw, e2] at e1
    exact e1.symm
  · intro e he u hu hhu
    have hw := hf3 e he _ (hmem u hu) (hhalf e u hhu)
    have e1 := hW.om_heis g h (pull g h u) f hf1
    have e2 : actO S T g h (pull g h u) = u := hact u
    rw [hw, e2] at e1
    exact e1.symm

end GlobalTheory.VacMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStrictUpperMemFlagUnipotentRadical
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvFlag

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

theorem form_vecX {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (b : Fin ρ → AE D) (y : VA V) :
    form V y (vecX d b) = (fun i => cA D (b i)) ⬝ᵥ (d.pY *ᵥ y) := by
  have h1 : (fun i => cA D (vecX d b i)) = (d.jX.map (cA D)) *ᵥ (fun i => cA D (b i)) := by
    funext i
    exact RingHom.map_mulVec (cA D) d.jX b i
  rw [form, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have hp : d.pY = adj d.jX * gA V := by
    rw [HypDec.pY, HypDec.qY, HypDec.jX, gA, ← rat_conjTranspose]
    exact Matrix.map_mul
  conv_rhs => rw [hp, ← Matrix.mulVec_mulVec]
  rfl

theorem mul_eq_of_cols {R : Type} [CommRing R] {n ρ : ℕ} (M : Matrix (Fin n) (Fin n) R) (E : Matrix (Fin n) (Fin ρ) R)
    (T : Matrix (Fin ρ) (Fin ρ) R)
    (h : ∀ k, M *ᵥ (E *ᵥ Pi.single k 1) = E *ᵥ Pi.single k 1 + E *ᵥ (fun i => T i k)) : M * E = E + E * T := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one T k, h k]
  rfl

theorem transv_mem_flagN : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (b : Fin ρ → AE D)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V),
    (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (Pi.single k 1)) v * b i = 0) →
    ∀ u : GA D V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d b) v u → u ∈ flagN d := by
  intro D V V₀ ρ d b v hb u hu
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  have hperp : ∀ y : VA V, d.pY *ᵥ y = 0 → act V u y = y + d.jX *ᵥ (form V y v • b) := by
    intro y hy
    rw [hu y, transv, form_vecX, hy, dotProduct_zero, zero_smul, sub_zero, mul_zero, zero_smul, sub_zero,
      Matrix.mulVec_smul]
    rfl
  refine ⟨⟨Matrix.of fun i k => form V (vecX d (Pi.single k 1)) v * b i, fun j i hij => hb j i hij, ?_⟩,
    fun y hy => ⟨form V y v • b, hperp y hy⟩⟩
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1]
  refine mul_eq_of_cols _ _ _ fun k => ?_
  have hp : d.pY * d.jX = 0 := by
    have h := congrArg rat d.ee
    rw [rat_zero] at h
    rw [HypDec.pY, HypDec.qY, HypDec.jX]
    simpa only [rat, Matrix.map_mul] using h
  have hk : d.pY *ᵥ vecX d (Pi.single k 1) = 0 := by
    rw [vecX, Matrix.mulVec_mulVec, hp, Matrix.zero_mulVec]
  exact hperp _ hk

end GlobalTheory.TransvFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

variable {D : D7}

theorem linInd_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : LinearIndependent D.host.E d.e.transpose := by
  show LinearIndependent D.host.E (fun i : Fin ρ => fun k : Fin W.rank => d.e k i)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : d.e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : (d.e'ᴴ * W.gram * d.e) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rw [d.e'e, Matrix.one_mulVec] at h2
  intro i; exact congrFun h2 i

theorem gramQ_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : gramQ W d.e = 0 := by
  rw [gramQ, ← Matrix.mul_assoc]; exact d.ee

theorem flagUnipotent_anisotropic_projection_eq_one {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) :
    d.p0 ⬝ (mt W n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((flag_jacobi_structure D W W₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    ← Matrix.mul_assoc (mt W (d.levi u)) d.jX, d.levi_jX, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, Matrix.zero_mul, add_zero]

theorem Rgrp_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : Rgrp W (rat d.e) = jacGrp d := by
  have dec := flag_jacobi_structure D W W₀ ρ d
  ext r
  constructor
  · rintro ⟨u, hu, hr⟩
    have hs : d.levi u⁻¹ * r ∈ stabX d := by
      show mt W (d.levi u⁻¹ * r) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, show mt W r ⬝ d.jX = d.jX ⬝ u.1 from hr, ← Matrix.mul_assoc, d.levi_jX,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    obtain ⟨n, hn, h, he⟩ := (dec.2.2.1 _).1 hs
    have hl : d.levi u ∈ flagN d := (dec.1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩
    refine (dec.2.2.2.1 r).2 ⟨d.levi u * n, mul_mem hl (Subgroup.mem_inf.1 hn).1, h, ?_⟩
    rw [mul_assoc, ← he, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · intro hr
    obtain ⟨n, hn, h, rfl⟩ := (dec.2.2.2.1 r).1 hr
    obtain ⟨u, hu, b, c, rfl⟩ := (dec.1 n).1 hn
    refine ⟨u, hu, ?_⟩
    show mt W _ ⬝ d.jX = d.jX ⬝ u.1
    rw [mt_mul, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.nC_jX, d.nB_jX,
      d.levi_jX]

theorem flagUnipotent_mul_emb_mem_rational_iff {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) (h : GA D W₀) :
    n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  constructor
  · intro hg
    have hh : h ∈ GQ W₀ := by
      rw [mem_GQ_iff] at hg ⊢
      have e : mt W₀ h = d.p0 ⬝ (mt W (n * d.emb0 h) ⬝ d.j0) := by
        rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt W n), ← Matrix.mul_assoc, flagUnipotent_anisotropic_projection_eq_one d hn,
          Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem _) (ratMx_mul hg (rat_mem _))
    refine ⟨?_, hh⟩
    have : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem hg (inv_mem (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hh))
  · rintro ⟨h1, h2⟩
    exact mul_mem h1 (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h2)

theorem base_point : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  intro D W W₀ ρ d
  refine ⟨⟨linInd_e d, fun u _ => ?_⟩, gramQ_e d, rfl, Rgrp_eq d, d.continuous_embed, fun n hn h => flagUnipotent_mul_emb_mem_rational_iff d hn h⟩
  rw [gramQ_e d, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilPairing

theorem thPair_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ (v : VolM D T.rank S.rank) p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → thPair v.μ v.𝓕 (om p f) (om p f') = thPair v.μ v.𝓕 f f' := by
  intro D ψ S T χ χ' om hW v p f f' hf hf'
  obtain ⟨hμ, h𝓕, -⟩ := v.covol
  have h𝓕' : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := h𝓕
  exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std S T v.μ v.𝓕 hμ h𝓕' (om p) (fun g hg => hW.om_pres p g hg)
    (fun g hg => hW.om_unit v.μ v.𝓕 hμ h𝓕' p g hg) f f' hf hf'

end GlobalTheory.WeilPairing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
section
namespace I195MixedCoordinates_ea4eb4ab36e967232c52358e

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

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_ea4eb4ab36e967232c52358e

public noncomputable abbrev _root_.I195MixedCoordinates_17a8b2bea10b408d05673c6f.source :=
  @_root_.I195MixedCoordinates_ea4eb4ab36e967232c52358e.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.MixCont

variable {D : D7}

theorem continuous_covolOne_integral {P : Type} [TopologicalSpace P] {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕) (F : P → Mx D m n → ℂ) (hF : Continuous (Function.uncurry F))
    (hper : ∀ p, ∀ γ ∈ ratMx D m n, ∀ a, F p (γ + a) = F p a) : Continuous fun p => ∫ a in 𝓕, F p a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  have hc : ∀ p, Continuous (F p) := fun p => hF.comp (continuous_const.prodMk continuous_id)
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod (s := Set.univ) (q := p₀) hF.continuousOn (Set.mem_univ _)
    (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  have hb : ∀ a ∈ 𝓕, ‖F p a - F p₀ a‖ ≤ ε / 2 := by
    intro a _
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hper p γ hγ a, ← hper p₀ γ hγ a, ← dist_eq_norm]
    exact (hvK p hp _ ha).le
  rw [dist_eq_norm, ← integral_sub (covolOne_integrableOn h _ (hc p) (hper p))
    (covolOne_integrableOn h _ (hc p₀) (hper p₀))]
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := 𝓕) (by rw [h.2.2]; exact ENNReal.one_lt_top) hb
  refine lt_of_le_of_lt h1 ?_
  simp [Measure.real, h.2.2]
  linarith

theorem integrandT_periodic_of_quasi {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ)
    {f : WO S T → ℂ} (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (y : Mx D S.rank σ)
    (w₀ : WO S T₀) (γ : Mx D σ S.rank) (hγ : γ ∈ ratMx D σ S.rank) (ξ : Mx D σ S.rank) :
    heisO ψ S T (d.incX S (γ + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 =
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
  obtain ⟨δ, hδ⟩ : d.incX S γ ∈ ratMx D _ _ := ratMx_mul (rat_mem _) hγ
  have h := hq δ (d.incX S ξ + d.incAdj S y + d.inc0 S w₀)
  rw [show ratW T S δ = d.incX S γ from hδ] at h
  rw [HypDec.integrandT_eq, HypDec.integrandT_eq, map_add (d.incX S), add_assoc (d.incX S γ), add_assoc (d.incX S γ), h,
    ← mul_assoc, ← AddChar.map_add_eq_mul]
  simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.symplOH_incX_incX,
    HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, zero_add, add_zero]
  rw [add_comm (symplOH S T (d.incX S γ) _), add_neg_cancel_right]

theorem mixed_coords_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle)
    (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ Φ, IsThetaFunO ψ V W Φ →
    (Continuous fun q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W =>
      (_root_.I195MixedCoordinates_ea4eb4ab36e967232c52358e.source dV) W ψ vS.μ vS.𝓕 (om q.1 Φ) q.2.1 q.2.2) ∧
    (Continuous fun q : (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀ =>
      evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (om q.1 Φ) q.2.1 q.2.2.1 q.2.2.2) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hw Φ hΦ
  have hψ : Continuous ψ := hw.std.1.1
  have hJ : Continuous fun p : (GA D V × GA D W) × WO V W => om p.1 Φ p.2 := GlobalTheory.Unf.jointCont_all D ψ V W χV χW om hw Φ hΦ
  have hth : ∀ p, IsThetaFunO ψ V W (om p Φ) := fun p => hw.om_pres p Φ hΦ
  have cX : Continuous (dV.extX W) := continuous_id.matrix_mul continuous_const
  have cY : Continuous (dV.extY W) := continuous_id.matrix_mul continuous_const
  have c0 : Continuous (dV.ext0 W) := continuous_id.matrix_mul continuous_const
  have h1 : Continuous fun q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W =>
      (_root_.I195MixedCoordinates_ea4eb4ab36e967232c52358e.source dV) W ψ vS.μ vS.𝓕 (om q.1 Φ) q.2.1 q.2.2 := by
    refine continuous_covolOne_integral vS.covol
      (fun (q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) a => heisO ψ V W (dV.extY W a)
        (heisO ψ V W (dV.extX W q.2.1) (heisO ψ V W (dV.ext0 W q.2.2) (om q.1 Φ))) 0) ?_ ?_
    · have e : Function.uncurry (fun (q : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) a => heisO ψ V W (dV.extY W a)
          (heisO ψ V W (dV.extX W q.2.1) (heisO ψ V W (dV.ext0 W q.2.2) (om q.1 Φ))) 0) =
          fun z => ψ (symplOH V W (dV.extY W z.2) (dV.extX W z.1.2.1)) *
            om z.1.1 Φ (dV.extY W z.2 + dV.extX W z.1.2.1 + dV.ext0 W z.1.2.2) := by
        funext z; exact dV.integrandS_eq _ _ _ _
      rw [e]
      refine (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cY.comp continuous_snd)
        (cX.comp (continuous_fst.snd.fst)))).mul ?_
      exact hJ.comp (continuous_fst.fst.prodMk (((cY.comp continuous_snd).add (cX.comp continuous_fst.snd.fst)).add
        (c0.comp continuous_fst.snd.snd)))
    · intro q γ hγ a
      exact dV.integrandS_periodic (hth q.1) q.2.1 q.2.2 γ hγ a
  refine ⟨h1, ?_⟩
  have cXT : Continuous (dW.incX V₀) := continuous_const.matrix_mul continuous_id
  have cA : Continuous (dW.incAdj V₀) := by
    have e : (dW.incAdj V₀ : Mx D V₀.rank σ → WO V₀ W) =
        fun y : Mx D V₀.rank σ => dW.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA V₀)) := by
      funext y; rfl
    rw [e]
    have h3 : Continuous fun y : Mx D V₀.rank σ => adj y ⬝ gA V₀ := continuous_adj.matrix_mul continuous_const
    have h4 : Continuous fun y : Mx D V₀.rank σ => incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA V₀) :=
      h3.const_smul (incA D (-D.host.xi0⁻¹))
    exact continuous_const.matrix_mul h4
  have cI : Continuous (dW.inc0 V₀) := continuous_const.matrix_mul continuous_id
  let G : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W → ℂ := fun q => (_root_.I195MixedCoordinates_ea4eb4ab36e967232c52358e.source dV) W ψ vS.μ vS.𝓕 (om q.1 Φ) q.2.1 q.2.2
  have h2 : Continuous fun (q : (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) =>
      ∫ ξ in vT.𝓕, ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ q.2.2.1)) *
        G (q.1, q.2.1, dW.incX V₀ ξ + dW.incAdj V₀ q.2.2.1 + dW.inc0 V₀ q.2.2.2) ∂vT.μ := by
    refine continuous_covolOne_integral vT.covol
      (fun (q : (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank σ × WO V₀ W₀) ξ =>
        ψ (symplOH V₀ W (dW.incX V₀ ξ) (dW.incAdj V₀ q.2.2.1)) *
        G (q.1, q.2.1, dW.incX V₀ ξ + dW.incAdj V₀ q.2.2.1 + dW.inc0 V₀ q.2.2.2)) ?_ ?_
    · refine (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cXT.comp continuous_snd)
        (cA.comp continuous_fst.snd.snd.fst))).mul ?_
      exact h1.comp (continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk
        (((cXT.comp continuous_snd).add (cA.comp continuous_fst.snd.snd.fst)).add (cI.comp continuous_fst.snd.snd.snd))))
    · intro q γ hγ ξ
      have := integrandT_periodic_of_quasi dW
        (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 (hth q.1) q.2.1 δ w) q.2.2.1 q.2.2.2 γ hγ ξ
      rw [HypDec.integrandT_eq, HypDec.integrandT_eq] at this
      exact this
  refine h2.congr fun q => ?_
  simp only [evalAt, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target, G]
  congr 1
  funext ξ
  exact (dW.integrandT_eq _ _ _ _).symm

end GlobalTheory.MixCont
end
end

