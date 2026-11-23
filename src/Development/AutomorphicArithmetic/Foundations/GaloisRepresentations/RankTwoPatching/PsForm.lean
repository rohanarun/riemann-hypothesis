module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.SplitTr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter ValuativeRel

namespace UpperTheory.Gal.SV

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem psForm {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (L : LawsT a ha rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ξ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hξ : ∀ i, IsSmoothChar (ξ i)) (hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ)) (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) :
    rc (algNorm σ) = (sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i)))).lpTw ((1 - (n : ℝ)) / 2) := by
  have : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  let k := w.adicCompletion E
  have hl : Unl (GroundTheory.LocalField.residueCard k) (GlobalTheory.RoadU.chars ξ hξ) := by
    intro χ ⟨c, hc⟩ χ' ⟨b, hb⟩ h1 hv
    apply hu _ hb _ hc
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    obtain ⟨⟨h₁, h₂⟩, eq_of_unram, -⟩ := polFacts k
    have hval : valuation k (unif k : k) = uniformizer k := by
      obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
      exact le_antisymm (le_uniformizer_iff.2 h₁) (hy ▸ h₂ y (hy ▸ uniformizer_lt_one))
    have hA : ((absPow k 1 (unif k) : ℂˣ) : ℂ) * (resCard k : ℂ) = 1 := by
      have hq : (resCard k : ℂ) ≠ 0 := by
        have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
        exact_mod_cast this.ne'
      rw [val_absPow, Complex.cpow_one, GlobalTheory.GLDoubling.nabs_unif hval]
      push_cast
      exact inv_mul_cancel₀ hq
    refine eq_of_unram χ' (χ * absPow k 1) ?_ ?_
    · have he : χ' * (χ * absPow k 1)⁻¹ = (χ * χ'⁻¹)⁻¹ * (absPow k 1)⁻¹ := by
        simp only [mul_inv, inv_inv]
        rw [← mul_assoc, mul_comm χ' χ⁻¹]
      rw [he]
      exact isUnram_mul (isUnram_inv h1) (isUnram_inv (isUnram_absPow k 1))
    · refine Units.ext ?_
      change _ = (resCard k : ℂ) at hv
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val] at hv
      rw [← hv] at hA
      rw [MonoidHom.mul_apply, Units.val_mul]
      have h0 : ((χ' (unif k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp at hA
      rw [mul_comm, hA]
  obtain ⟨e⟩ := unlFull (w.adicCompletion E) n σ.V σ.ρ ξ hξ hs' hl
  let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hL : IsL ((List.ofFn fun i => Segment.single (y i) (hy i) : List (Segment k)) :
      Multiset (Segment k)) σ.ρ := by
    have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
    have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i =>
      Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    have hnl : ∀ i j, ¬ (Segment.single (y i) (hy i)).Linked (Segment.single (y j) (hy j)) := fun i j =>
      GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j)
        (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j))
    have hP : (prodIrr y hd).IsIrreducible :=
      GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd hnl
        (fun i => (single_spec (hy i)).2.1)
    obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
      (stdBlocks (fun i => (y i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ξ i))
    let q := multiProdEquiv (stdBlocks (fun i => (y i).1) hd) fun i =>
      equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i))
    have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
        fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
    have hprin : (prinSeries ξ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e σ.irred
    obtain ⟨e₁⟩ := (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries
      (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ξ).nonempty_equiv hM hprin
    have φ : σ.ρ.Equiv (prodIrr y hd) := (e.trans e₁).trans (p.trans q)
    exact ⟨n, y, hd, ⟨fun i => Segment.single (y i) (hy i), ⟨Fin.univ_val_map _, fun i j _ hp => hnl i j hp.1⟩,
      fun i => (single_spec (hy i)).2.1⟩, (isCosocle_self σ.irred).of_equiv (.refl _) φ⟩
  have hL' := hL.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL', segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, y, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, GlobalTheory.LocLanglands.Test.lpChar_lpSp_one, L.one]
  rw [algNorm, L.nu, hr]

open scoped commutatorElement in
theorem gdOf : GdOf := by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hA := psForm L σ ξ hξ (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm) hu
  refine ⟨?_, ?_⟩
  · have hd : (rc (algNorm σ)).lpDim = n := by
      rw [L.dim]
      rfl
    intro s t
    have comm_one {G H : Type} [Group G] [CommGroup H] (f : G →* H) (s t : G) :
        f ⁅s, t⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    show WD.charPol _ _ = _
    rw [hd, hA, GlobalTheory.GalCut.AwayMono.charPol_lpTw, comm_one,
      GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn]
    have hchar (i : Fin n) :
        (WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))).charPol ⁅s, t⁆ = X - 1 := by
      rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp only [comm_one]
      simp
    simp [hchar, List.prod_ofFn]
  · rw [hA, WD.monomial_twist_iff]
    have sum_mono0 (l : List (WD h)) (hl : ∀ z ∈ l, z.mono0) : (sumList l).mono0 := by
      induction l with
      | nil =>
        show (WD.lpZero (h := h)).mono0
        rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]
        rfl
      | cons b l ih =>
        show (WD.lpSum b (sumList l)).mono0
        exact (WD.monomial_sum_iff _ _).2 ⟨hl b (by simp), ih fun z hz => hl z (by simp [hz])⟩
    refine sum_mono0 _ fun z hz => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
    rw [WD.lpOfChar, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    rfl

theorem recTr (hG : GlobalTheory.Published.GlobalArtinReciprocity) {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {u : HeightOneSpectrum (𝓞 K)} {h' : IsPlaceOver A u} {j : E →+* K} {i : w.adicCompletion E ≃+* u.adicCompletion K}
    (P : PlaceIso A w A u (RingEquiv.refl Ω) j i) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin n) (u.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V)
    (he : ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))
    {rc : IrrGL (k := w.adicCompletion E) → WD h} {rc' : IrrGL (k := u.adicCompletion K) → WD h'} (hrc : IsRecT h rc) (hrc' : IsRecT h' rc')
    (hP : GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)) :
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) := by
  obtain ⟨a, ha, L⟩ := hrc
  obtain ⟨a', ha', L'⟩ := hrc'
  have hi := P.cont
  have hi' : Continuous i.symm := GlobalTheory.LocalFieldIso.continuous_symm i hi
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hρ : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  let ξ' : Fin n → (u.adicCompletion K)ˣ →* ℂˣ := fun k => (ξ k).comp (Units.map i.symm.toRingHom.toMonoidHom)
  have hξ' : ∀ k, IsSmoothChar (ξ' k) := fun k =>
    IsOpen.preimage (f := Units.map i.symm.toRingHom.toMonoidHom) (Continuous.units_map _ hi') (hξ k)
  have h5 : ∀ t, Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom t) = t := fun t =>
    Units.ext (i.symm_apply_apply _)
  have hg : ∀ g : GL (Fin n) (u.adicCompletion K),
      Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (σ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) σ'.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨e.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change e (σ.ρ (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) x) = σ'.ρ g (e x)
      rw [he, hg]⟩ e.bijective
  have h3 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hρ).of_equiv φ
  have h4 : (GlobalTheory.RoadU.chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') = GlobalTheory.RoadU.chars ξ' hξ' := by
    rw [GlobalTheory.RoadU.chars, GlobalTheory.RoadU.chars, Multiset.map_map]
    exact Multiset.map_congr rfl fun k _ => GlobalTheory.DegOneChar.trGL_ofChar i hi' (ξ k) (hξ k) (hξ' k)
  rw [h4] at h3
  have hu' : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ' hξ') := by
    intro y hy z hz heq
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at heq
    refine hu _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)) _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val m)) ?_
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    refine MonoidHom.ext fun t => ?_
    have h6 := DFunLike.congr_fun heq (Units.map i.toRingHom.toMonoidHom t)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, h5, GlobalTheory.LocalFieldIso.absPow_map i hi] at h6
    exact h6
  obtain ⟨S, hS, -, h0, hsum, -, hSt, -, -, hch⟩ := GlobalTheory.WDTransport.exists_equiv_wd E Ω A w h K Ω A u h' (RingEquiv.refl Ω) j i P
  have hl : ∀ l : List (WD h), S (sumList l) = sumList (l.map S) := fun l => by
    induction l with
    | nil => exact h0
    | cons b l ih => exact (hsum b (sumList l)).trans (congrArg (WD.lpSum (S b)) ih)
  refine (hS _ _).2 ?_
  rw [psForm L σ ξ hξ hρ hu, psForm L' σ' ξ' hξ' h3 hu', hSt, hl, List.map_ofFn]
  congr 2
  refine List.ofFn_inj.mpr (funext fun k => hch _ _ _ _ fun s s' hss => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    _root_.GlobalTheory.LocLanglands.isLocalArtin_transport hG GlobalTheory.Published.chevalleyUnits' E Ω A w h K Ω A u h' _ j i P a a' ha ha' s s' hss]
  exact (congrArg (ξ k) (h5 _)).symm

def RatioT : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc →
    ∀ (a : ℕ) (π : CuspSub K a) (t : ℝ), WinAt π t w → ∀ σ, π.IsLocComp w σ → UpperTheory.GalN.V.RatioW (rc (algNorm σ))

end UpperTheory.Gal.SV
