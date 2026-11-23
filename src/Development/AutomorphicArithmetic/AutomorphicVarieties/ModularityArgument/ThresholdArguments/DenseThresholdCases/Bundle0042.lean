module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdExtChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.ToTL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FixedDvd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (Polynomial.X - 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
private theorem UpperTheory.V.Z.Win.T2.char_of_dvd {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ) (hM : 1 ≤ M) (x z : WD h)
    (hx : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      x.charPol (ineIncl h s) = (Polynomial.X - 1) ^ n)
    (hz : IsIrrWD z) (hd : ∀ σ, z.charPol σ ∣ x.charPol σ) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h2 := hd (ineIncl h s)
    rw [hx s hs, WD.charPol_mk] at h2
    exact UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩
private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2
private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩
theorem UpperTheory.V.Z.Win.T2.fixedDvd' :
    _root_.UpperTheory.V.Lev.fixedDvd_s_ty := by
  intro P F Ω _ _ _ _ _ n M hM w hw A h rc hrc σ hL
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  have hv : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := UpperTheory.V.Z.Win.T2.val_lt_one w hw
  have hM0 : (M : w.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (w.adicCompletion F)), map_ne_zero]
    exact Nat.cast_ne_zero.2 (by omega)
  have hu0 : uniformizer (w.adicCompletion F) ≠ 0 := by simp
  have hv0 : valuation (w.adicCompletion F) (M : w.adicCompletion F) ≠ 0 := by simpa using hM0
  let γ : (ValueGroupWithZero (w.adicCompletion F))ˣ :=
    Units.mk0 (valuation _ (M : w.adicCompletion F) / uniformizer (w.adicCompletion F)) (div_ne_zero hv0 hu0)
  have hlt : ∀ x : ValueGroupWithZero (w.adicCompletion F),
      x < γ ↔ x ≤ valuation _ (M : w.adicCompletion F) := fun x => by
    show x < _ / _ ↔ _
    rw [lt_div_iff₀ (zero_lt_iff.2 hu0)]
    refine ⟨fun h1 => not_lt.1 fun h2 => h1.not_ge ?_, fun h1 => (mul_le_mul_left h1 _).trans_lt
      (mul_lt_of_lt_one_right (zero_lt_iff.2 hv0) uniformizer_lt_one)⟩
    have hx : 0 < x := (zero_lt_iff.2 hv0).trans h2
    rwa [← div_le_iff₀' hx, le_uniformizer_iff, div_lt_one₀ hx]
  have hγ : γ ≤ 1 := by
    show _ / _ ≤ (1 : ValueGroupWithZero (w.adicCompletion F))
    rw [div_le_one₀ (zero_lt_iff.2 hu0), le_uniformizer_iff]
    exact hv
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport P.litN.loc.zel (algNorm σ)
  have hch : ∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : (w.adicCompletion F)ˣ,
      valuation (w.adicCompletion F) ((u : w.adicCompletion F) - 1) < γ → χ u = 1 := fun y hy => by
    obtain ⟨ξ, hξ, e, hξ1⟩ := UpperTheory.V.Z.Win.T2.char_of_dvd w A h M n hM _ (rc y) hL ((H.cusp y).1 (hs.isCusp hy)) fun τ => by
      rw [H.supp _ s hs τ]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol τ) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    refine ⟨χ, hχ, H.inj _ _ (UpperTheory.V.Z.Win.T2.good_ofChar χ hχ) (e.trans (H.one χ hχ).symm), fun u hu => ?_⟩
    obtain ⟨τ, rfl⟩ := ha.surj u
    have h1 : valuation (w.adicCompletion F) (a τ : w.adicCompletion F) = 1 := by
      have := (valuation (w.adicCompletion F)).map_one_add_of_lt (hu.trans_le (Units.val_le_val.2 hγ))
      simpa using this
    obtain ⟨h2, h3⟩ := UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence P.litN.aut.art F Ω w A h a ha M hM τ h1 ((hlt _).1 hu)
    exact hξ1 ⟨τ, h2⟩ h3
  have hne := UpperTheory.jacquet_borel_nontrivial_of_character_support P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s hs fun y hy => by
    obtain ⟨χ, hχ, rfl, -⟩ := hch y hy
    rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_borel_exists_torus_congruence_fixed P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s γ hγ hs hch hne
  have hf := UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed _ _ _ (algNorm σ).rep γ hγ
    ((P.litN.loc.bz _).1 _ _ _ (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr) y hy0 hy
  refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hf
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, fun i j => (hlt _).2 ((UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).2 i j)⟩, hv0⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Win.T2.laArtinLit' :
    _root_.UpperTheory.V.Loc.localArtinReciprocity_type := by
  intro N F Ω _ _ _ _ _ A w h
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt N h
  obtain ⟨a, ha, ε, -⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  exact ⟨a, ha⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdAtLOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord.AtLOrdinary
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem plainTor_of_ps [CharZero k] {n : ℕ} (σ : SmIrr (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo k, ω i y ≠ ω j y) (e : σ.ρ.Equiv (PS ω)) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2)) := fun i => (hs i).mul (isSmoothChar_absPow _)
  have hsup := hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)
  refine ⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e'
    by_cases hij : i = j
    · subst hij
      have h1 : absPow k ((1 : ℝ) : ℂ) = 1 := by
        have := mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')
        simpa using this.symm
      exact one_ne_zero (absPow_ofReal_eq_one.1 h1)
    · obtain ⟨y, hy⟩ := hd i j hij
      have h1 := DFunLike.congr_fun e' (y : kˣ)
      simp only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1
      exact hy h1
end UpperTheory.V.Z.Ord.AtLOrdinary
open UpperTheory.V.Z.Ord.AtLOrdinary in
theorem UpperTheory.V.Z.Ord.at_l_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → AtLOf := by
  intro _ l _ L Ω _ _ _ _ _ ι n A w h r HT τ lam hHT hLG hw ω hs hd ⟨e⟩ rc hrc _ O _ _ _ Bw hj
  haveI : CharZero (w.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  have hP := plainTor_of_ps τ ω hs hd e
  have hG : Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  obtain ⟨h1, h2⟩ := hHT hP A h O Bw hj
  refine ⟨h1, fun t LL' τ' hτ => ?_, fun s => ?_⟩
  · have hemb : ∃ j : UpperTheory.V.W.Emb l w,
        j.1.comp (algebraMap L (w.adicCompletion L)) = t := by
      have hplace : w = GlobalTheory.EvExtend.placeOf t := by
        refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
        rw [GlobalTheory.EvExtend.mem_placeOf, hτ]
        let f := LL'.1.val.comp τ'
        let y : Bw.Kw.1 := ⟨Bw.j (algebraMap L Ω x), Bw.j_E x⟩
        have hnorm : ‖f y‖ = ‖(y : PadicAlgCl l)‖ := by
          rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm,
            spectralNorm, minpoly.algHom_eq f f.injective,
            ← minpoly.algHom_eq Bw.Kw.1.val Bw.Kw.1.val.injective]
          rfl
        refine ((hj.valuation_lt_one_iff _).symm.trans (h x)).symm.trans ?_
        exact iff_of_eq (congrArg (· < 1) hnorm.symm)
      rw [hplace]
      obtain ⟨j, hc, hx, -⟩ := GlobalTheory.EvExtend.exists_ext t
      exact ⟨⟨j, hc⟩, RingHom.ext hx⟩
    obtain ⟨j, rfl⟩ := hemb
    have e : HT (j.1.comp (algebraMap L _)) =
        Finset.univ.val.map fun i => htW lam i (j.1.comp (algebraMap L _)) := by
      refine Multiset.map_injective (f := fun k : ℤ => (k : ℂ)) Int.cast_injective ?_
      rw [hw j]
      simp only [infOfWeight, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [htW, lowW, Function.comp_apply, DomWeight.dual]
      push_cast
      ring
    have h3 := h2 _ LL' τ' hτ
    rw [e] at h3
    exact h3
  · rw [((hLG A h rc hrc).2 O Bw hj hG).2]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdThruL
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open GlobalTheory.Pst GlobalTheory.TripleGal Module
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag
section Tri
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
private theorem tri_dR (T : LocTied l P AI) (Bw : LocBridge l E Ω (Dec (F := E) A) O) (LL : FinExt l) (n : ℕ) :
    ∀ (r : ↥(Dec (F := E) A) →* GL (Fin n) ↥LL.1) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1),
    (∀ g i j, j < i → (r g).val i j = 0) → (∀ g i, (r g).val i i = (c i g).val 0 0) →
    Bw.IsdRE P LL r → ∀ i, Bw.IsdRE P LL (c i) := by
  induction n with
  | zero => exact fun _ _ _ _ _ i => i.elim0
  | succ n ih =>
    intro r c hr hc hd
    obtain ⟨r', hr'⟩ := UpperTheory.V.Loc.PstExact.exists_tail r hr
    obtain ⟨h1, h2⟩ := UpperTheory.V.Loc.PstExact.exact_line (k := ↥LL.1) (n := n)
    have h3 := LinearMap.funLeft_surjective_of_injective ↥LL.1 ↥LL.1 _ (Fin.succ_injective n)
    have hi : ∀ g v, ((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) (Bw.repE LL (c 0) g v) =
        Bw.repE LL r g (((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, hc, Fin.sum_univ_succ]
      · simp [Matrix.mulVec, dotProduct, hr _ j.succ 0 (Fin.succ_pos j), Fin.sum_univ_succ]
    have hp : ∀ g v, LinearMap.funLeft ↥LL.1 ↥LL.1 (Fin.succ : Fin n → Fin (n + 1)) (Bw.repE LL r g v) =
        Bw.repE LL r' g (LinearMap.funLeft ↥LL.1 ↥LL.1 Fin.succ v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, hr _ i.succ 0 (Fin.succ_pos i), Fin.sum_univ_succ, hr']
    obtain ⟨d₀, d₂, -⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T Bw.Kw LL _ _ _ _ _ _ _ _ hi hp h1 h3
      h2.linearMap_ker_eq.symm (by rw [IsDR, finrank_fin_fun]; exact hd)
    rw [IsDR, finrank_fin_fun] at d₀ d₂
    have hq := ih r' (fun i => c i.succ) (fun g i j hij => by rw [hr', hr g _ _ (Fin.succ_lt_succ_iff.2 hij)])
      (fun g i => by rw [hr', hc]) d₂
    exact fun i => Fin.cases d₀ hq i
private theorem flag_jumps (T : LocTied l P AI) (Bw : LocBridge l E Ω (Dec (F := E) A) O) {n : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin n) (Om l)) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) (Om l))
    (M : GL (Fin n) (Om l)) (hr : ∀ g i j, j < i → (M * r g * M⁻¹).val i j = 0)
    (hc : ∀ g i, (M * r g * M⁻¹).val i i = (c i g).val 0 0) (τ : E →+* Om l) (J : Multiset ℤ)
    (hJ : IsJumpsAt P Bw r τ J) (i : Fin n) : ∃ a, IsJumpsAt P Bw (c i) τ {a} := by
  let r' : ↥(Dec (F := E) A) →* GL (Fin n) (Om l) := (MulAut.conj M).toMonoidHom.comp r
  have hr' : ∀ g, r' g = M * r g * M⁻¹ := fun _ => rfl
  obtain ⟨L, r₂, hm, hd, τ₂, hτ, -⟩ := (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw n r r' M hr').2.2.2 τ J hJ
  obtain ⟨c₂, hm', hc₂⟩ := UpperTheory.V.Loc.PstExact.exists_diag Bw (r := r') hc hm
  have htri : ∀ g i j, j < i → (r₂ g).val i j = 0 := fun g i j hij => Subtype.ext (by
    have := hr g i j hij
    rw [← hr', ← hm.2] at this
    exact this)
  have hdr := tri_dR T Bw L n r₂ c₂ htri hc₂ hd i
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE L (c₂ i)) := by
    rw [IsDR, finrank_fin_fun]
    exact hdr
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ L _ (Bw.repE L (c₂ i))).1 τ₂
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _ ((c₂ i).comp Bw.e.symm.toMonoidHom) τ₂ hfin
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 (h1.trans ((hrk hdr').trans (finrank_fin_fun _)))
  exact ⟨a, L, c₂ i, hm' i, hdr, τ₂, hτ, h2⟩
end Tri
section Loc
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
private theorem emb_norm (j : W.Emb l w) (x : 𝓞 L) : ‖j.1.comp (algebraMap L _) (x : L)‖ < 1 ↔ x ∈ w.asIdeal := by
  have h1 : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (y : L)) = w.valuation L (algebraMap (𝓞 L) L y) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hy
    have h3 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h2)
    simpa [Function.comp_def] using h3
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h1, GlobalTheory.EvExtend.mem_placeOf]
private theorem cont_of_flag {n : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩
private theorem ord_of_flag (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    {a : Weil h →* (w.adicCompletion L)ˣ} (ha : IsLocalArtin h a) {n : ℕ} {r : ↥(Dec (F := L) A) →* GL (Fin n) (Qbar l)} (hr : Continuous r)
    {ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : Induces Bw) (HT : (L →+* Qbar l) → Multiset ℤ)
    (hJ : ∀ (τ : L →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt (Loc.PP l) Bw r τ (HT τ)) :
    ∃ (hh : Fin n → (L →+* Qbar l) → ℤ) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), ∀ i, OrdChar ι a (ω i) (hh i) (ψ i) := by
  classical
  have art := N.aut.art
  have hD : GlobalTheory.Published.HeckeLAdicCharacterDeRham := by
    intro E Ω _ _ _ _ _ l _ P AI ht ι art ha χ n μ h1 h2 h3 w A hA O _ _ _ Bw hB
    have := N.aut.chA E Ω l P AI ht ι art ha χ n μ h1 h2 h3 w A hA O Bw hB
    exact ⟨this.1, this.2.2.2⟩
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨M, hM⟩ := hf
  have hf' : W.HasFlag r ψ := ⟨M, hM⟩
  have hone : ∀ (i : Fin n) (j : W.Emb l w), ∃ b, IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) (j.1.comp (algebraMap L _)) {b} := fun i j => by
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CharAboveRead.exists_isInduced_of _ w hw (emb_norm j) A h O Bw hj
    exact flag_jumps T Bw r (fun i => rk1 (ψ i)) M (fun g => (hM g).1)
      (fun g i => ((hM g).2 i).trans (by simp [rk1])) _ _ (hJ _ _ τ' hτ') i
  let hh : Fin n → (L →+* Qbar l) → ℤ := fun i τ =>
    if hx : ∃ b, IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) τ {b} then hx.choose else 0
  have hs : ∀ (i : Fin n) (j : W.Emb l w),
      IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) (j.1.comp (algebraMap L _)) {hh i (j.1.comp (algebraMap L _))} := fun i j => by
    simp only [hh, dif_pos (hone i j)]
    exact (hone i j).choose_spec
  have hc := cont_of_flag hr hf'
  have hla := fun i => UpperTheory.V.Loc.laConv art art.heckeLAdicCharacter hD N.aut.berger h (ψ i) (hc i) O Bw hj
    (fun j => hh i (j.1.comp (algebraMap L _))) (hs i)
  choose ω hω using fun i => (UpperTheory.V.Loc.ordCharIff art h ι a ha (hh i) (ψ i)).1.2 ⟨hc i, hla i⟩
  exact ⟨hh, ω, hω⟩
private theorem pol_of_flag (N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    {a : Weil h →* (w.adicCompletion L)ˣ} (ha : IsLocalArtin h a) {n : ℕ} {r : ↥(Dec (F := L) A) →* GL (Fin n) (Qbar l)}
    {ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : Induces Bw) (hp : IsPstAt (Loc.PP l) Bw r)
    {hh : Fin n → (L →+* Qbar l) → ℤ} {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} (hω : ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) (s : Weil h) :
    (wdAt (Loc.PP l) ι Bw h hj r).charPol s = ∏ i, (X - C ((ω i (a s) : ℂˣ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hc := fun i => (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l N h hw ι a ha (ω i) (hh i) (ψ i) (hω i)).1 O Bw hj
  obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj _ (fun i => rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [rk1]))
  rw [(F₂ hp).2 s]
  exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s
end Loc
private theorem mem_of_prod {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∏ j, (X - C (f j x)) = ∏ j, (X - C (g j x))) (j : Fin n) : ∃ i, g i = f j := by
  have hc := GlobalTheory.CharDeg.card_fiber_eq_of_sum_eq f g (fun x => GlobalTheory.CharDeg.sum_eq_of_prod_eq _ _ (h x)) (f j)
  haveI : Nonempty {i // f i = f j} := ⟨⟨j, rfl⟩⟩
  haveI : Finite {i // g i = f j} := inferInstance
  have hpos : 0 < Nat.card {i // g i = f j} := hc ▸ Nat.card_pos
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact ⟨i, hi⟩
end UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag
open UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag GroundTheory.Global.SemiLocal UpperTheory.V.Z.Win UpperTheory.V.Z.Gam UpperTheory.Zero.LLC UpperTheory.V.Af in
theorem UpperTheory.V.Z.Ord.thruL_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → Win.PlainRec → Win.Thru true := by
  intro Pr hPR hRow K L Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r hc hIne P hreg hpol hatt v hv hpot w t hwin s hs ζ hζ hmem
  obtain ⟨σ, hσ, hsup⟩ := hs
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed K, inferInstance⟩
  haveI : CharZero (w.1.adicCompletion L) := charZero_of_injective_algebraMap (algebraMap L _).injective
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w.1
  have hAv : IsPlaceOver A v := by
    have e : w.1.under (𝓞 K) = v := by
      ext1
      exact (Ideal.over_def w.1.asIdeal v.asIdeal).symm
    exact e ▸ GlobalTheory.AboveL.SatBC.isPlaceOver_under hA
  have hlv : ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := hv.2 rfl
  have hlw : ((l : ℕ) : 𝓞 L) ∈ w.1.asIdeal := by
    rw [Ideal.over_def w.1.asIdeal v.asIdeal, Ideal.under, Ideal.mem_comap] at hlv
    simpa using hlv
  set rL : G L Ω →* GL (Fin n) (Qbar l) := r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) with hrL
  have hcL : Continuous rL := hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom K L Ω)
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w.1 hA
  obtain ⟨HT, -, hC⟩ := UpperTheory.V.Z.Win.compatTOf hRow hPR L Ω l ι n (by omega) rL P hcL hreg hpol hatt
  obtain ⟨hPT, hTor, hMono⟩ := hPR L Ω A w.1 hA rc hrc n P t hwin σ hσ
  obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) hA hlw
  have hHT := (hC w.1 σ hσ).2 hPT A hA O Bw hj
  obtain ⟨hpst, hwd⟩ := ((hC w.1 σ hσ).1 A hA rc hrc).2 O Bw hj ⟨hTor, hMono⟩
  obtain ⟨κ, hκ, -⟩ := hpot rfl A hAv
  let res : ↥(Dec (F := L) A) →* ↥(Dec (F := K) A) :=
    ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω).comp (Dec (F := L) A).subtype).codRestrict _ fun g => g.2
  let ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ := fun i => (κ i).comp res
  have hκf : W.HasFlag (r.comp (Dec (F := K) A).subtype) κ := hκ
  have hfL : W.HasFlag (rL.comp (Dec (F := L) A).subtype) ψ := by
    obtain ⟨M, hM⟩ := hκf
    exact ⟨M, fun g => hM (res g)⟩
  have hcD : Continuous (rL.comp (Dec (F := L) A).subtype) := hcL.comp continuous_subtype_val
  have hcK : Continuous (r.comp (Dec (F := K) A).subtype) := hc.comp continuous_subtype_val
  obtain ⟨a, ha, hLaws⟩ := hrc
  obtain ⟨hh, ω, hω⟩ := ord_of_flag Pr.litN ι hA hlw ha hcD hfL Bw hj HT hHT.2
  have hpolW : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ∏ i, (X - C ((ω i (a g) : ℂˣ) : ℂ)) := fun g => by
    rw [← hwd]
    exact pol_of_flag Pr.litN ι hA hlw ha hfL Bw hj hpst hω g
  obtain ⟨ξ, hξ, hsupx, -⟩ := GlobalTheory.RoadU.plainTor_exists_chars (w.1.adicCompletion L) (IrrGL.of σ.ρ σ.smooth σ.irred) hPT
  let c : ℂ := (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  let ξ' : Fin n → ((w.1.adicCompletion L)ˣ →* ℂˣ) := fun j => ξ j * absPow _ c
  have hξ' : ∀ j, IsSmoothChar (ξ' j) := fun j => (hξ j).mul (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsup' : HasSupport (algNorm σ).rep (GlobalTheory.RoadU.chars ξ' hξ') :=
    (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.1.adicCompletion L) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ ξ' hξ hξ' c fun _ => rfl).1.1 hsupx
  have hpolC : ∀ g : Weil hA, (rc (algNorm σ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := fun g =>
    charPol_of_chars hLaws _ ξ' hξ' hsup' g
  obtain ⟨hG, hZ⟩ := GlobalTheory.geometricLemma_and_zelevinskyPolynomialRing
  have hse : s = GlobalTheory.RoadU.chars ξ hξ := GlobalTheory.LocGL.SupportUnique.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hZ _
    (IrrGL.of σ.ρ σ.smooth σ.irred) _ _ (hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)) hsupx
  obtain ⟨j, -, hj'⟩ := Multiset.mem_map.1 (hse ▸ hmem)
  have hζj : ξ j = ζ := IrrGL.ofChar_inj.1 hj'
  let f : Fin n → (Weil hA →* ℂ) := fun j => (Units.coeHom ℂ).comp ((ξ' j).comp a)
  let g : Fin n → (Weil hA →* ℂ) := fun i => (Units.coeHom ℂ).comp ((ω i).comp a)
  obtain ⟨i, hi⟩ := mem_of_prod f g (fun x => (hpolC x).symm.trans (hpolW x)) j
  obtain ⟨χ, hχ, hu⟩ := _root_.UpperTheory.V.Z.Ord.ext_character_of_literal_automorphy_n Pr.litN K L Ω l ι v w A hA hlv a ha (κ i) (ψ i)
    (cont_of_flag hcK hκf i) (fun x y e => congrArg (κ i) (Subtype.ext e.symm)) (ω i) (hh i) (hω i)
  refine ⟨χ, hχ, fun x hx1 => ?_⟩
  have e := hu x hx1
  obtain ⟨y, rfl⟩ := ha.surj x
  have e1 : ω i (a y) = ξ' j (a y) := Units.ext (DFunLike.congr_fun hi y)
  have e' : ξ' j (a y) = ξ j (a y) := by
    simp only [ξ', MonoidHom.mul_apply, isUnram_absPow _ c _ hx1, mul_one]
  rw [MonoidHom.mul_apply] at e ⊢
  rw [← hζj, ← e', ← e1]
  exact e
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVConv
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.SV
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
theorem ratioW_of_hasSat_alt [IsTotallyReal F] (_P : _root_.UpperTheory.V.Af.Hypotheses') {n : ℕ} {π : TR.CuspSub F n} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT) {w : HeightOneSpectrum (𝓞 F)}
    (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    UpperTheory.GalN.V.RatioW (wdOf h hl ι r) := H.ratio w hl A h (H.plain w B hB)
end UpperTheory.Gal.SV
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ToTL
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.P
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem toTL'_alt (_N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (k : IsRecT h rc) : IsRecT h rc := k
end UpperTheory.V.Z.Desc.P
end
end

