module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantPDivGroupOmegaTrivialHodgeTateBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n k : ℕ} {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin k) E}


omit [NumberField E] in
theorem scalesBy_mul {p q : GAd σ J} {β γ : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β)
    (e' : ScalesBy σ J X q γ) : ScalesBy σ J X (p * q) (β * γ) := by
  unfold ScalesBy at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Units.val_mul, Matrix.mul_assoc]


omit [NumberField E] in
theorem scalesBy_inv {p : GAd σ J} {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β) :
    ScalesBy σ J X p⁻¹ β⁻¹ := by
  unfold ScalesBy at *
  calc (matHom _ σ J p⁻¹).1 * adMat F X = (matHom _ σ J p⁻¹).1 * (adMat F X * β.1 * (β⁻¹).1) := by
        rw [Matrix.mul_assoc (adMat F X), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F X * (β⁻¹).1 := by
        rw [← e]; simp only [Matrix.mul_assoc]
    _ = adMat F X * (β⁻¹).1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem absE_pos (u : (AF F ⊗[F] E)ˣ) : (0 : ℝ) < absE F E u := by
  have h : absE F E u * absE F E u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

theorem isCompact_isHt_scales : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h H
  haveI := H.lat
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll H.cm J L a
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx H.cm H.herm H.witt
  have hsc : ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
    intro p β e g
    obtain ⟨q, γ, e', k, hk, rfl⟩ := H.iwa g
    rw [← mul_assoc, H.ht _ _ (scalesBy_mul e e') _ hk, H.ht _ _ e' _ hk, map_mul, map_mul, NNReal.coe_mul]
  let φ : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun p =>
    adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X)
  have h1 : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hyx]; simp
  have hφ : ∀ p β, ScalesBy σ J X p β → φ p = β.1 := fun p β e => by
    unfold ScalesBy at e
    show adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X) = β.1
    rw [e, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have cφ : Continuous φ := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  let P := GlobalTheory.StdPar.frameStab σ J X (⊤ : Subgroup (GL (Fin (r + 1)) (AF F ⊗[F] E)))
  have cP : IsClosed (P : Set (GAd σ J)) := GlobalTheory.StdPar.isClosed_frameStab hyx isClosed_univ
  have hP : ∀ p : P, ScalesBy σ J X p.1 p.2.choose := fun p => p.2.choose_spec.2
  let u : P → (AF F ⊗[F] E)ˣ := fun p => Matrix.GeneralLinearGroup.det p.2.choose
  have cu : Continuous u := Units.continuous_iff.2
    ⟨((cφ.comp continuous_subtype_val).matrix_det).congr fun p => by
        simp only [Function.comp, u, hφ _ _ (hP p)]; rfl,
      ((cφ.comp (continuous_subtype_val.inv)).matrix_det).congr fun p => by
        show (φ (p.1⁻¹)).det = _
        rw [hφ _ _ (scalesBy_inv (hP p)), ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨hK, ⟨fun g => ?_, ?_, fun k hk => by simpa using H.ht 1 1 (by simp [ScalesBy]) k hk, fun g => ?_⟩, hsc⟩
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    rw [H.ht _ _ e _ hk]; exact absE_pos _
  · refine GlobalTheory.Doubling.continuous_of_prod cP hK
      (fun g => let ⟨p, β, e, k, hk, e'⟩ := H.iwa g; ⟨⟨p, β, trivial, e⟩, k, hk, e'⟩) ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (cu.comp continuous_fst))).congr
      fun x => (H.ht _ _ (hP x.1) _ x.2.2).symm
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, hsc _ _ e, H.ht _ _ e _ hk]

end GlobalTheory.ResidueEisenstein.HtCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat.PairLatLattice

variable {E : Type} [Field E] [NumberField E]

theorem scLat_isLattice {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.scLat 𝔞 Λ) := by
  have hinv : 𝔞⁻¹ ≠ 0 := inv_ne_zero h𝔞
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hinv)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔞)
  have hb' : b ∈ 𝔞⁻¹ := hb
  have ha' : a ∈ 𝔞 := ha
  refine ⟨?_, ?_⟩
  ·
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
      (LinearMap.lsmul E (Fin n → E) b⁻¹).restrictScalars (𝓞 E)
    have hle : GlobalTheory.SkewLat.scLat 𝔞 Λ ≤ Λ.map f := by
      intro y hy
      refine ⟨b • y, hy b hb', ?_⟩
      simp [f, smul_smul, mul_inv_cancel₀ hb0]
    exact Submodule.FG.of_le (Submodule.FG.map f hΛ.fg) hle
  ·
    have hmem : ∀ y ∈ Λ, a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
      intro y hy c hc
      have hca : c * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← inv_mul_cancel₀ h𝔞]
        exact FractionalIdeal.mul_mem_mul hc ha'
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hca
      rw [smul_smul, ← hr, algebraMap_smul]
      exact Λ.smul_mem r hy
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem prod_span_eq_top {a b : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsFullLattice E M) (hN : Submodule.IsFullLattice E N) :
    Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E))) = ⊤ := by
  set S := Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E)))
  have hl : ∀ x : Fin a → E, (x, 0) ∈ S := by
    have : Submodule.span E (M : Set (Fin a → E)) ≤ S.comap (LinearMap.inl E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show (m, (0 : Fin b → E)) ∈ M.prod N from ⟨hm, N.zero_mem⟩)
    intro x
    have hx : x ∈ Submodule.span E (M : Set (Fin a → E)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hM)]; trivial
    exact this hx
  have hr : ∀ y : Fin b → E, (0, y) ∈ S := by
    have : Submodule.span E (N : Set (Fin b → E)) ≤ S.comap (LinearMap.inr E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show ((0 : Fin a → E), m) ∈ M.prod N from ⟨M.zero_mem, hm⟩)
    intro y
    have hy : y ∈ Submodule.span E (N : Set (Fin b → E)) := by rw [Submodule.IsFullLattice.span_eq_top (self := hN)]; trivial
    exact this hy
  apply top_unique
  intro ⟨x, y⟩ _
  simpa using S.add_mem (hl x) (hr y)
theorem pairLat_isLattice {a b d : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsLattice E M) (hN : Submodule.IsLattice E N) (e : Fin a ⊕ Fin b ≃ Fin d) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat M N e) := by
  let φ : (Fin d → E) ≃ₗ[E] (Fin a → E) × (Fin b → E) :=
    (LinearEquiv.funCongrLeft E E e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ E E)
  have hφ : GlobalTheory.SkewLat.pairLat M N e = (M.prod N).map (φ.symm.restrictScalars (𝓞 E)).toLinearMap := by
    ext x
    rw [Submodule.mem_map_equiv, GlobalTheory.SkewLat.mem_pairLat]
    rfl
  rw [hφ]
  refine ⟨Submodule.FG.map _ (Submodule.FG.prod hM.fg hN.fg), ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.SkewLat.PairLatLattice

open GlobalTheory.SkewLat.PairLatLattice in
theorem GlobalTheory.SkewLat.pairLat_scLat_isLattice : ∀ {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 →
    ∀ {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}, Submodule.IsLattice E ΛA →
    Submodule.IsLattice E ΛB → ∀ (e : Fin a ⊕ Fin b ≃ Fin d),
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat 𝔞 ΛA) (GlobalTheory.SkewLat.scLat 𝔞 ΛB) e) := by
  intro E _ _ a b d 𝔞 h𝔞 ΛA ΛB hA hB e
  exact pairLat_isLattice (scLat_isLattice h𝔞 hA) (scLat_isLattice h𝔞 hB) e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfIntegers
section
noncomputable section

open WittVector CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConstDatum

theorem isLocalRing_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra h
  push_neg at h
  have h1 : v (algebraMap O C a) < 1 :=
    lt_of_le_of_ne (hv.map_le_one a) (fun e => h.1 (hv.isUnit_of_one' e))
  have h2 : v (algebraMap O C (1 - a)) < 1 :=
    lt_of_le_of_ne (hv.map_le_one _) (fun e => h.2 (hv.isUnit_of_one' e))
  have h3 := v.map_add (algebraMap O C a) (algebraMap O C (1 - a))
  have h4 : algebraMap O C a + algebraMap O C (1 - a) = 1 := by rw [← map_add (f := _)]; simp
  rw [h4, v.map_one] at h3
  exact lt_irrefl _ (lt_of_le_of_lt h3 (max_lt h1 h2))

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem etale_al (ε : PreTilt O p) (h : ℕ) (y : Fin h → O) : (etale ε h).al y = y := by
  simp [Datum.al, etale, Matrix.map_one _ (map_zero _) (map_one _)]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : fontaineTheta O p (Sandwich.mu ε) = 0 := by
  rw [Sandwich.mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

theorem etale_bb {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) (y : Fin h → O) :
    (etale ε h).bb y = 0 := by
  ext i
  simp [Datum.bb, etale, Matrix.mulVec, dotProduct, theta_mu hε]

theorem etale_Fil {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (h : ℕ) : (etale ε h).Fil = ⊤ :=
  eq_top_iff.2 fun y _ => etale_bb hε h y

end GlobalTheory.ConstDatum


open GlobalTheory.ConstDatum in
theorem GlobalTheory.PDivLat.hasDatum_of_isConst : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConst G → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG
  haveI := GlobalTheory.PointGroup.isIntegrallyClosedIn_of_integers hv
  haveI := isLocalRing_of_integers hv
  obtain ⟨hω, hbij⟩ := _root_.GlobalTheory.ConstHT.omega_const p C v O hv G hG
  haveI := GlobalTheory.PointGroup.finite_tate hv G
  haveI := GlobalTheory.PointGroup.free_tate hv G
  have hrank : Module.finrank ℤ_[p] G.Tate = G.height := G.finrank_tate C
  let e : G.Tate ≃ₗ[ℤ_[p]] (Fin G.height → ℤ_[p]) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank, Module.finrank_fin_fun])
  let b : Module.Basis (Fin G.height) ℤ_[p] G.Tate := Module.Basis.ofEquivFun e
  let Φ := LinearEquiv.ofBijective _ (hbij G.height b)
  let D := etale ε G.height
  have hF : D.Fil = ⊤ := etale_Fil hε G.height
  let fil : G.dual.omega ≃ₗ[O] D.Fil := Φ.symm ≪≫ₗ (LinearEquiv.ofTop _ hF).symm
  haveI : Subsingleton G.Lie :=
    ⟨fun f g => LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, map_zero]⟩
  haveI : Subsingleton ((Fin G.height → O) ⧸ D.Fil) :=
    ⟨fun a b => by
      obtain ⟨a, rfl⟩ := D.Fil.mkQ_surjective a
      obtain ⟨b, rfl⟩ := D.Fil.mkQ_surjective b
      exact (Submodule.Quotient.eq D.Fil).2 (by rw [hF]; exact Submodule.mem_top)⟩
  refine ⟨D, e, fil, LinearEquiv.ofSubsingleton _ _, fun t => ?_, fun x χ => ?_⟩
  · rw [etale_al]
    change toO e t = ((LinearEquiv.ofTop _ hF).symm (Φ.symm (hodgeTate G t)) : Fin G.height → O)
    rw [LinearEquiv.coe_ofTop_symm_apply, LinearEquiv.eq_symm_apply]
    change Fintype.linearCombination O (fun i => hodgeTate G (b i)) (toO e t) = hodgeTate G t
    rw [Fintype.linearCombination_apply]
    have hb : b.equivFun = e := Module.Basis.equivFun_ofEquivFun e
    conv_rhs => rw [← b.sum_equivFun t]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hb]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hodgeTate_smul (padicToO p O)]
    rfl
  · rw [Subsingleton.elim x 0]
    simp [pairingO]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.WeilM
open Filter Topology

theorem isLocallyConstant_finprod_evalV {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hcof : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    IsLocallyConstant (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hy : ∀ᶠ v in Filter.cofinite, ∀ i,
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.mono fun v hv => hv
  set T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
    {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F)} with hT
  have hTfin : T.Finite := hcof.and hy
  have hO : IsOpen {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have hU : ∀ᶠ y' in 𝓝 y, ∀ i, ∀ v, (y' i - y i) v ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i :=
      (continuous_apply i).sub continuous_const
    have hmem : (fun y' : κ → FiniteAdeleRing (𝓞 F) F => y' i - y i) y ∈
        {z : FiniteAdeleRing (𝓞 F) F | ∀ v, z v ∈ v.adicCompletionIntegers F} := by
      intro v
      simp only [sub_self]
      exact zero_mem _
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)
  have hS : ∀ᶠ y' in 𝓝 y, ∀ v ∈ T, (φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) =
      φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) := by
    refine (Filter.eventually_all_finite hTfin).2 fun v _ => ?_
    have hg : Continuous fun y' : κ → FiniteAdeleRing (𝓞 F) F =>
        fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    exact ((IsLocallyConstant.iff_eventually_eq _).1 ((hφ v).1.comp_continuous hg)) y
  filter_upwards [hU, hS] with y' hU' hS'
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ T
  · exact hS' v hv
  · have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
        ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      simpa [hT] using hv
    obtain ⟨h1, h2⟩ := hv'
    have h3 : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) ∈ v.adicCompletionIntegers F := by
      intro i
      have h4 := add_mem (hU' i v) (h2 i)
      have h5 : (y' i - y i) v + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i) =
          Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i) := by
        show (y' i) v - (y i) v + (y i) v = (y' i) v
        exact sub_add_cancel _ _
      rwa [h5] at h4
    rw [h1, Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y' i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3),
      Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
    rfl

end GlobalTheory.WeilM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlaces
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem isLocalHom_constantCoeff_ps (O : Type) [CommRing O] [IsLocalRing O] :
    IsLocalHom (PowerSeries.constantCoeff (R := O)) :=
  ⟨fun _ ha => PowerSeries.isUnit_iff_constantCoeff.2 ha⟩

private theorem constantCoeff_comp_sc {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) :
    (PowerSeries.constantCoeff (R := E)).comp (sc p u) = p.O.subtype.comp (PowerSeries.constantCoeff (R := p.O)) := by
  refine RingHom.ext fun a => ?_
  show PowerSeries.constantCoeff (PowerSeries.rescale u (PowerSeries.map p.O.subtype a)) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, _root_.one_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rfl

private theorem spMap_comp_spMap {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem evAt_eq_of_eq {R : Type} [CommRing R] {X : Scheme.{0}} {a b : Sp R ⟶ X} (e : a = b) {U : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U) : evAt a h = evAt b h' := by
  subst e; rfl

theorem isRatPath_of_integral_at_places : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ ξ u hu0 hfin hpos hloc
  choose b ζ hb hpath hξ using hloc
  have hFF : IsFF k E := (_root_.GlobalTheory.Nef.isFF_main k K (_root_.GlobalTheory.Nef.CurveFF.isFF_of_isGenOver k K C x hx)).2 E
  obtain ⟨p₀, -⟩ : ∃ p, ord p (u p) ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [finsum_eq_zero_of_forall_eq_zero hc] at hpos
    exact lt_irrefl _ hpos
  apply _root_.GlobalTheory.Nef.isRatPath_of_isRat E G.left ξ
  intro U _ h f
  set V : C.Opens := unitSec G ⁻¹ᵁ U with hV
  have hVne : (V : Set C).Nonempty := by
    let q : Sp E := IsLocalRing.closedPoint E
    refine ⟨(spMap p₀.O.subtype ≫ b p₀) q, ?_⟩
    have h2 : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = spMap p₀.O.subtype ≫ b p₀ ≫ unitSec G := by
      rw [hξ p₀, ← Category.assoc, spMap_comp_spMap, constantCoeff_comp_sc, ← spMap_comp_spMap, Category.assoc,
        (hpath p₀).zero]
    have h3 : (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) q ∈ U := h trivial
    rw [h2] at h3
    exact h3
  have hfinb := GlobalTheory.T.finite_places_centre_outside_open k K E C x hx V hVne
  have hUp : ∀ p, ⊤ ≤ (spMap (sc p (u p)) ≫ ζ p) ⁻¹ᵁ U := fun p => hξ p ▸ h
  choose e ψ he0 he1 heq using fun p => _root_.GlobalTheory.Nef.den_along_path k E p (u p) G.left (ζ p) U (hUp p) f
  have key : ∀ p, ⊤ ≤ (b p) ⁻¹ᵁ V → ⊤ ≤ (ζ p) ⁻¹ᵁ U := by
    intro p hp
    haveI := isLocalHom_constantCoeff_ps p.O
    rw [_root_.GlobalTheory.Nef.evAt_calculus.2.2.2.1 (PowerSeries p.O) G.left (ζ p) U]
    rw [← (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := p.O)) :
      spMap (PowerSeries.constantCoeff (R := p.O)) (IsLocalRing.closedPoint p.O) = _)]
    show (spMap (PowerSeries.constantCoeff (R := p.O)) ≫ ζ p) (IsLocalRing.closedPoint p.O) ∈ U
    rw [(hpath p).zero]
    exact hp trivial
  refine _root_.GlobalTheory.RatCrit.isRat_of_adelic k E hFF (evAt ξ h f) u e ψ hu0 hfin hpos he0 ?_ ?_
  · refine hfinb.subset fun p hp => ⟨b p, hb p, fun hbV => hp ?_⟩
    rw [he1 p (key p hbV), map_one]
    exact isUnit_one
  · intro p
    rw [evAt_eq_of_eq (hξ p) h (hUp p)]
    exact heq p

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOOfMatchedSquareBigRoute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RouteSeesaw

theorem isThetaFunO_of_isMatched : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G μ₀ _hL W B ρ t i j Θ Θ' hM d hd
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, hF, rfl, -⟩ := hM
  obtain ⟨e, -, -, φ₁, φ₂, hφ, -⟩ := hF
  unfold tensT at hd
  obtain ⟨P, -, hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  have hd := Finsupp.support_single_subset hd
  rw [Finset.mem_singleton] at hd
  subst hd
  obtain ⟨h₁, h₂⟩ := hφ d' hd'
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2.2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2.2
  exact ⟨GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₁.2 v₁),
    GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₂.2 v₂)⟩

end GlobalTheory.RouteSeesaw
end

