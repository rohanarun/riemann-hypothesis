module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0245
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinEquiv
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem bkStr_quotient_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  intro l _ a _ O _ _ π Ep hE hπ
  obtain ⟨hmon, -, hdvd, -⟩ := hE
  obtain ⟨h0, hsurj, hker⟩ := hπ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn)
      monic := hmon }
  have hK : RingHom.ker (Polynomial.aeval (R := Wq l a) π) = Ideal.span {Ep} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · exact hker f
    · rintro ⟨g, rfl⟩
      simp [h0]
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π)
    (fun x => hsurj x)
  let e2 := Ideal.quotientEquivAlgOfEq (Wq l a) hK
  let e := (e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv
  refine ⟨e, fun f => ?_⟩
  have h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f := by
    apply e1.injective
    simp only [AlgEquiv.apply_symm_apply, e1]
    rfl
  simp only [e, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]
  simp [e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelian
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B hp hE hA hord hcomm hpow hnot
  obtain ⟨j, hj, hrange, -, hram⟩ := _root_.GlobalTheory.PMon.Ram.baseChange_fixedField K L A
  have hmemA : ∀ σ, j σ ∈ A := fun σ => hrange.le ⟨σ, rfl⟩
  have htop : lowerRamificationGroup (IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hram, eq_top_iff]
    intro σ _
    exact hA (hmemA σ)
  have hcomm' : ∀ σ τ : L ≃ₐ[IntermediateField.fixedField A] L,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ B.comap j := by
    intro σ τ
    rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (hmemA σ) _ (hmemA τ)
  have hpow' : ∀ σ : L ≃ₐ[IntermediateField.fixedField A] L, σ ^ p ∈ B.comap j := by
    intro σ
    rw [Subgroup.mem_comap, map_pow]
    exact hpow _ (hmemA σ)
  have hne : B.comap j ≠ ⊤ := by
    intro h
    apply hnot
    intro a ha
    obtain ⟨σ, rfl⟩ := hrange.ge ha
    have : σ ∈ B.comap j := h ▸ Subgroup.mem_top σ
    exact this
  have key := _root_.GlobalTheory.PMon.Ram.card_le_jumpSum_wild_of_exponent (IntermediateField.fixedField A) L p E (B.comap j) hp hE htop hord
    hcomm' hpow' hne
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  have hcard : Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) = Nat.card ↥A := by
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans
      (congrArg (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card ↥H) hrange)
  have hjs : jumpSum (wild K L) A B =
      jumpSum (wild (IntermediateField.fixedField A) L) ⊤ (B.comap j) := by
    rw [hwild, _root_.GlobalTheory.PMon.Ram.jumpSum_comap_injective _ _ j (wild K L) B hj]
    exact congrArg (fun H => jumpSum (wild K L) H B) hrange.symm
  calc Nat.card ↥A = Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) := hcard.symm
    _ ≤ _ := key
    _ = jumpSum (wild K L) A B := hjs.symm

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs
section
noncomputable section

namespace GlobalTheory.Pass.CentralStep

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepCentral := by
  intro _ D P i s
  classical
  have hcard : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g D.nd) := by
    rw [D.nd.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change _ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  haveI : Finite (G0g D.nd) := Nat.finite_of_card_ne_zero (hcard ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  have key : ∀ L : List (Σ k : Fin 2, D.nd.PlG k),
      let e := (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod
      e * e = e ∧ ∀ z, e * z = z * e := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      obtain ⟨h1, h2⟩ := ih
      have hc := Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D a.1 a.2 _
        (D.ntypes.eSer_central a.1 (s a)))
      have hi : ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) * ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) =
          ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) := by
        rw [GlobalTheory.SeriesSupportTest.atPlace_eq, ← map_mul, D.ntypes.eSer_idem]
      simp only [List.map_cons, List.prod_cons]
      refine ⟨?_, fun z => ?_⟩
      · rw [mul_assoc, ← mul_assoc _ (ArithmeticCylinders.atPlace D a.1 a.2 _), hc, mul_assoc, h1, ← mul_assoc, hi]
      · rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
  obtain ⟨h1, h2⟩ := key Finset.univ.toList
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  obtain ⟨z, hz, hz'⟩ := GlobalTheory.CentralIdem.card_mul_idem_from_center D i (G0g D.nd) _ h1 h2
    ⟨ζ, hcard ▸ hζ.map_of_injective hinj⟩
  refine ⟨⟨z, hz⟩, Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩
  ext h
  rw [hcard]
  simpa [PairedCharacterCondition.mapCoef] using hz' h

end GlobalTheory.Pass.CentralStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CobOfGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

noncomputable section

namespace GlobalTheory.LocalH2Injective


open GlobalTheory.TateTop in
theorem cob_of_gen {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [ContinuousMul Γ] [CompactSpace Γ] {χ : Γ →* ℤ_[l]ˣ} (hχ : Continuous fun g => (χ g : ℤ_[l]))
    (hG : ∀ r, ∃ c, GlobalTheory.TateTop.Gen χ (r + 1) c)
    {B' B : Type} [AddCommGroup B'] [Module ℤ_[l] B'] [Finite B'] [AddCommGroup B] [Module ℤ_[l] B]
    (f : B' →ₗ[ℤ_[l]] B) (hf : Function.Injective f)
    (htor : ∀ b : B, ∃ n : ℕ, (l : ℤ_[l]) ^ n • b = 0) (z : Γ × Γ → B') (c : Γ → B)
    (hc : IsLocallyConstant c) (hz : ∀ p, f (z p) = cob χ c p) :
    ∃ c' : Γ → B', IsLocallyConstant c' ∧ ∀ p, z p = cob χ c' p := by
  classical
  have hfinS : (Set.range c ∪ Set.range f).Finite := hc.range_finite.union (Set.finite_range f)
  obtain ⟨r, hfin, hkill⟩ := finite_span (l := l) htor hfinS
  set M := Submodule.span ℤ_[l] (Set.range c ∪ Set.range f) with hMdef
  have : Finite M := hfin
  have hM : ∀ m : M, (l : ℤ_[l]) ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hkill m, smul_zero]
  let fM : B' →ₗ[ℤ_[l]] M :=
    f.codRestrict M (fun b => Submodule.subset_span (Or.inr ⟨b, rfl⟩))
  have hfM : Function.Injective fM := fun a b hab => hf (congrArg Subtype.val hab)
  let cM : Γ → M := fun g => ⟨c g, Submodule.subset_span (Or.inl ⟨g, rfl⟩)⟩
  have hcM : IsLocallyConstant cM := IsLocallyConstant.desc cM Subtype.val hc Subtype.val_injective
  have hB' : ∀ b : B', (l : ℤ_[l]) ^ (r + 1) • b = 0 := by
    intro b
    apply hfM
    rw [map_smul, map_zero, hM]
  have hfz : (fun p => fM (z p)) = cob χ cM := by
    funext p
    apply Subtype.ext
    simp [fM, cM, cob, hz p]
  have hcoc := isCoc_cob hχ hM hcM
  have hzc : IsCoc χ z := by
    refine ⟨IsLocallyConstant.desc z fM (by rw [show ⇑fM ∘ z = fun p => fM (z p) from rfl, hfz]; exact hcoc.1) hfM, ?_⟩
    intro g h k
    apply hfM
    have e := hcoc.2 g h k
    rw [← hfz] at e
    simpa only [map_sub, map_add (f := _), map_smul, map_zero] using e
  obtain ⟨g0, hg0⟩ := hG r
  obtain ⟨x, b, hb, hzb⟩ := (hg0 B' hB').2.1 z hzc
  have hx : fM x = 0 := by
    refine (hg0 M hM).2.2 (fM x) (fun g => cM g - fM (b g))
      (hcM.comp₂ (hb.comp fM) (· - ·)) ?_
    intro p
    have h2 : fM (z p) = cob χ cM p := congrFun hfz p
    calc g0 p • fM x = fM (z p) - fM (cob χ b p) := by
          rw [hzb p, map_add (f := _), map_smul, add_sub_cancel_right]
      _ = cob χ cM p - cob χ (fun g => fM (b g)) p := by
          rw [h2]; simp only [cob, map_add (f := _), map_sub, map_smul]
      _ = cob χ (fun g => cM g - fM (b g)) p := by
          simp only [cob, smul_sub]; abel
  have hx0 : x = 0 := hfM (by rw [hx, map_zero])
  exact ⟨b, hb, fun p => by rw [hzb p, hx0, smul_zero, zero_add]⟩

theorem h2_inj : LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B' B : Type) [AddCommGroup B'] [Module O B'] [Finite B'] [AddCommGroup B] [Module O B] (f : B' →ₗ[O] B), Function.Injective f → (∀ b : B, ∃ n : ℕ, l ^ n • b = 0) → ∀ (z : Dec (F := F) A → Dec (F := F) A → B') (c : Dec (F := F) A → B), IsLocallyConstant c → (∀ g h, f (z g h) = algebraMap ℤ_[l] O ((cycZ F Ω l g.1 : ℤ_[l]ˣ) : ℤ_[l]) • c h - c (g * h) + c g) → ∃ c' : Dec (F := F) A → B', IsLocallyConstant c' ∧ ∀ g h, z g h = algebraMap ℤ_[l] O ((cycZ F Ω l g.1 : ℤ_[l]ˣ) : ℤ_[l]) • c' h - c' (g * h) + c' g := by
  intro hT F Ω _ _ _ _ _ l _ A v hA O _ _ B' B _ _ _ _ _ f hf htor z c hc hzc
  have : CompactSpace (Dec (F := F) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Dec (F := F) A).isCompact
  let : Module ℤ_[l] B' := Module.compHom B' (algebraMap ℤ_[l] O)
  let : Module ℤ_[l] B := Module.compHom B (algebraMap ℤ_[l] O)
  let fZ : B' →ₗ[ℤ_[l]] B :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun a x => f.map_smul (algebraMap ℤ_[l] O a) x }
  let χ : Dec (F := F) A →* ℤ_[l]ˣ := (cycZ F Ω l).comp (Dec (F := F) A).subtype
  have hχ : Continuous fun g => (χ g : ℤ_[l]) :=
    Units.continuous_val.comp ((continuous_cycZ F Ω l).comp continuous_subtype_val)
  have htorZ : ∀ b : B, ∃ n : ℕ, (l : ℤ_[l]) ^ n • b = 0 := by
    intro b
    obtain ⟨n, hn⟩ := htor b
    refine ⟨n, ?_⟩
    show algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ n) • b = 0
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn]
  have hG : ∀ r, ∃ c, GlobalTheory.TateTop.Gen χ (r + 1) c := by
    intro r
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let : TopologicalSpace (ZMod (l ^ (r + 1))) := ⊥
    have : DiscreteTopology (ZMod (l ^ (r + 1))) := ⟨rfl⟩
    refine GlobalTheory.TateTop.exists_gen hχ
      ((hT F Ω l (r + 1) (ZMod (l ^ (r + 1))) A
        (Representation.trivial (ZMod (l ^ (r + 1))) (Dec (F := F) A) (ZMod (l ^ (r + 1)))) v
        (Nat.succ_pos r) hA ?_).1) ?_
    · have htr : (fun p : Dec (F := F) A × ZMod (l ^ (r + 1)) =>
          Representation.trivial (ZMod (l ^ (r + 1))) (Dec (F := F) A) (ZMod (l ^ (r + 1)))
            p.1 p.2) = Prod.snd := by
        funext p
        simp
      show Continuous _
      rw [htr]
      exact continuous_snd
    · intro M _ _ _ _ _ rho hrho
      exact (hT F Ω l (r + 1) M A rho v (Nat.succ_pos r) hA hrho).2.2.2.2
  obtain ⟨c', hc', hzc'⟩ := cob_of_gen hχ hG fZ hf htorZ (fun p => z p.1 p.2) c hc
    (fun p => hzc p.1 p.2)
  exact ⟨c', hc', fun g h => hzc' (g, h)⟩

end GlobalTheory.LocalH2Injective
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrthV

theorem exists_unitLattice {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
      L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  have hχ : ∀ g, ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
    intro g
    refine Formalism.MainNotions.BlochKatoDuality.Br.zl_int hO _ ?_
    rw [P.PD_χ K g]
    obtain ⟨a, ha, _⟩ := P.χQ_cyc (g : GQ l) 0 1 (one_pow _)
    have h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by
      ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := hχ g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

theorem cocycle_mem_coboundaries_of_tate_orthogonal' : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm b hb horth
  obtain ⟨⟨hDom, hDVR, hFrac⟩, hfd, hmt, htr, hopen⟩ := id hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := htr
  haveI : IsTopologicalAddGroup A'.V := IsModuleTopology.topologicalAddGroup LL A'.V
  obtain ⟨L1, hL1⟩ := exists_unitLattice P K LL O hO
  obtain ⟨LA, LA', hLL', -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hT'open : IsOpen (LA'.T : Set A'.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA'.T LA'.fg LA'.span
  have hL1open : IsOpen (L1.T : Set LL) := by
    rw [hL1]
    have e : ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) =
        Set.range (algebraMap O LL) := by
      ext y; simp [Algebra.linearMap_apply]
    rw [e]; exact hopen
  have hp : ((l : ℕ) : LL) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

  have hcobZ : ∀ x : A'.V, (fun g => A'.ρ g x - x) ∈ continuousCocycles A'.ρ := by
    intro x
    refine ⟨(A'.cont x).sub continuous_const, fun g h => ?_⟩
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

  have key : ∀ n : ℕ, ∃ β ∈ latticeCocycles LA', b - ((l : LL) ^ n) • β ∈ B1 A'.ρ := by
    intro n
    set s : LL := (((l : ℕ) : LL) ^ n)⁻¹ with hs
    let c : ↥(GK K) → A'.V ⧸ LA'.T := fun g => Submodule.Quotient.mk (s • b g)
    have hcZ : c ∈ divisibleCocycles LA' := by
      refine ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA'.T hT'open _ (hb.1.const_smul s), fun g h => ?_⟩
      show Submodule.Quotient.mk (s • b (g * h)) = Submodule.Quotient.mk (s • b g) +
        actD LA' g (Submodule.Quotient.mk (s • b h))
      rw [hb.2 g h, smul_add, Submodule.Quotient.mk_add]
      congr 1
      show _ = Submodule.Quotient.mk (A'.ρ g (s • b h))
      rw [map_smul]
    have hcorth : ∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c) := by
      intro d hd
      obtain ⟨f, hfc, hf⟩ := horth d hd.1
      refine ⟨fun g => (Submodule.Quotient.mk (s • f g) : LL ⧸ L1.T),
        ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hL1open _ (hfc.const_smul s), fun _ => Submodule.mem_top⟩, ?_⟩
      funext x
      obtain ⟨g, h⟩ := x
      have hf' : ((cycLL (P.PD K) LL g : LLˣ) : LL) • f h - f (g * h) + f g =
          m (d g) (A'.ρ g (b h)) := congrFun hf (g, h)
      have hlift : liftD LA' (c h) - s • b h ∈ LA'.T :=
        (Submodule.Quotient.eq _).1 (Submodule.Quotient.mk_surjective LA'.T (c h)).choose_spec
      obtain ⟨e, he⟩ := (hLL'.2 _).1 (LA'.stable g _ hlift) (d g) (hd.2 g (Set.mem_univ g))
      show (Submodule.Quotient.mk (((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h)) : LL ⧸ L1.T) -
          Submodule.Quotient.mk (s • f (g * h)) + Submodule.Quotient.mk (s • f g) =
          Submodule.Quotient.mk (m (d g) (A'.ρ g (liftD LA' (c h))))
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hL1]
      have e1 : ((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h) - s • f (g * h) + s • f g =
          s • m (d g) (A'.ρ g (b h)) := by
        rw [← hf']; simp only [smul_eq_mul]; ring
      have e2 : m (d g) (A'.ρ g (liftD LA' (c h))) =
          s • m (d g) (A'.ρ g (b h)) + m (d g) (A'.ρ g (liftD LA' (c h) - s • b h)) := by
        simp only [map_sub, map_smul, add_sub_cancel]
      rw [e1, e2]
      refine ⟨-e, ?_⟩
      show algebraMap O LL (-e) = _
      rw [map_neg, ← he]
      abel
    obtain ⟨xbar, hx⟩ := GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m
      hLL' c hcZ hcorth
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective LA'.T xbar
    refine ⟨fun g => s • b g - (A'.ρ g x - x), ⟨(continuousCocycles A'.ρ).sub_mem ((continuousCocycles A'.ρ).smul_mem s hb) (hcobZ x),
      fun g _ => ?_⟩, ?_⟩
    · have hg : Submodule.Quotient.mk (A'.ρ g x) - Submodule.Quotient.mk x =
          (Submodule.Quotient.mk (s • b g) : A'.V ⧸ LA'.T) := congrFun hx g
      rw [← Submodule.Quotient.mk_sub] at hg
      exact (Submodule.Quotient.eq _).1 hg.symm
    · refine ⟨(((l : ℕ) : LL) ^ n) • x, ?_⟩
      funext g
      have hps : (((l : ℕ) : LL) ^ n) * s = 1 := mul_inv_cancel₀ (pow_ne_zero n hp)
      simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul,
        Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul, hps, one_smul]
      abel

  have hl : ((l : ℕ) : O) ∉ nonunits O → False := by
    intro hu
    have hu' : IsUnit ((l : ℕ) : O) := by simpa [mem_nonunits_iff] using hu
    have hc := (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO).2.2.2
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu'
    have h10 : (1 : O) = 0 := by
      apply hc.toIsHausdorff.haus 1
      intro n
      rw [htop, Ideal.top_pow, Submodule.top_smul]
      exact SModEq.top
    exact one_ne_zero h10
  have hne : Ideal.span {((l : ℕ) : O)} ≠ ⊤ := by
    intro htop
    apply hl
    intro hmem
    exact hmem (Ideal.span_singleton_eq_top.1 htop)
  haveI hfinH : Module.Finite O (LatticeCohomology LA') :=
    GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  let S : Submodule O ↥(latticeCocycles LA') := ((B1 A'.ρ).restrictScalars O).comap (latticeCocycles LA').subtype
  have hBS : (latticeCoboundaries LA').comap (latticeCocycles LA').subtype ≤ S := by
    rintro z ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  haveI : Module.Finite O (↥(latticeCocycles LA') ⧸ S) := by
    refine Module.Finite.of_surjective (Submodule.factor hBS) ?_
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥(latticeCocycles LA') ⧸ S) _ hne
  obtain ⟨β0, hβ0, hbβ0⟩ := key 0
  rw [pow_zero, one_smul] at hbβ0
  have hq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) = 0 := by
    rw [← Submodule.mem_bot O, ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨β, hβ, hbβ⟩ := key i
    have heq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) =
        (((l : ℕ) : O) ^ i) • Submodule.Quotient.mk ⟨β, hβ⟩ := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show β0 - (((l : ℕ) : O) ^ i) • β ∈ B1 A'.ρ
      have h1 : β0 - (((l : ℕ) : O) ^ i) • β = (b - ((l : LL) ^ i) • β) - (b - β0) := by
        rw [← algebraMap_smul LL (((l : ℕ) : O) ^ i) β, map_pow, map_natCast]
        abel
      rw [h1]
      exact (B1 A'.ρ).sub_mem hbβ hbβ0
    rw [heq, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hβ0B : β0 ∈ B1 A'.ρ := (Submodule.Quotient.mk_eq_zero S).1 hq
  have : b = (b - β0) + β0 := by abel
  rw [this]
  exact (B1 A'.ρ).add_mem hbβ0 hβ0B

end GlobalTheory.TateOrthV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.CMType

theorem isCMType_conj {E : Type} [Field E] {I : Type} (φ : I → E →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    IsCMType fun i => ComplexEmbedding.conjugate (φ i) := by
  unfold IsCMType
  intro σ
  have hmk : ∀ j, InfinitePlace.mk (φ j) = InfinitePlace.mk σ ↔
      (σ = ComplexEmbedding.conjugate (φ j) ∨
        σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j))) := by
    intro j
    have cc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)) = φ j := star_star (φ j)
    rw [InfinitePlace.mk_eq_iff, cc]
    constructor
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
  obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk σ)
  exact ⟨i, (hmk i).1 hi, fun j hj => h.1 (((hmk j).2 hj).trans hi.symm)⟩

theorem phi_cmType : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R),
    IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  intro R H
  obtain ⟨_, -, ⟨-, -, -, -, hbij⟩, -, hsq, -⟩ := GlobalTheory.Mem.HostCM.host_cm_embedding_properties R H
  refine ⟨isCMType_conj (embPsi H) hbij, fun g g' => ?_⟩
  show ComplexEmbedding.conjugate (embPsi H g) H.sqrtMinusD =
    ComplexEmbedding.conjugate (embPsi H g') H.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hsq g, hsq g']

end GlobalTheory.LamTie.CMType
end

