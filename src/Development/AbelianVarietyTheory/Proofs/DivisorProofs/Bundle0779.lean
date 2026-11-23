module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113
public import Formalism.LocalToGlobal.Columns.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitNormGramDetRationalApproximation
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
section
noncomputable section

namespace GlobalTheory.ColNorms.DatOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

section Generic

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem mem_lamY_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) :
    v ∈ LocE.lamY P q n c ex ↔ ∀ l : Fin (n + c), Formalism.L2.Col.IntAt P (((q : E) ^ LocE.scE n ex l.1)⁻¹ * v l) := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap]
  exact mem_localization_standardLattice P _

theorem proj_mem {P : HeightOneSpectrum (𝓞 E)} {q n c : ℕ} {ex : ℕ → ℕ} {v : Sp E (n + c)} (hv : v ∈ LocE.lamY P q n c ex) :
    LinearMap.funLeft E E (Fin.castAdd c) v ∈ stdAt E n P := by
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := (mem_lamY_iff P q n c ex v).1 hv (Fin.castAdd c i)
  simpa [LocE.scE, LinearMap.funLeft_apply] using h

theorem proj_inX {n c : ℕ} (y : Sp E n) : LinearMap.funLeft E E (Fin.castAdd c) (Loc.inX E n c y) = y := by
  funext i
  simp [LinearMap.funLeft_apply, Loc.inX]

theorem inX_mem_iff (P : HeightOneSpectrum (𝓞 E)) (q n c : ℕ) (ex : ℕ → ℕ) (y : Sp E n) :
    Loc.inX E n c y ∈ LocE.lamY P q n c ex ↔ y ∈ stdAt E n P := by
  constructor
  · intro h
    simpa [proj_inX] using proj_mem h
  · intro h
    refine (mem_lamY_iff P q n c ex _).2 fun l => ?_
    by_cases hl : l.1 < n
    · have := (mem_localization_standardLattice P _).1 h ⟨l.1, hl⟩
      simpa [LocE.scE, Loc.inX, hl] using this
    · have := Formalism.L2.Col.IntAt.coe P (0 : 𝓞 E)
      simpa [Loc.inX, hl] using this

theorem joinCol_inX {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (y : Sp E n') :
    (joinCol x₀ y' : HomE E (n' + c') (n + c)) (Loc.inX E n' c' y) = Loc.inX E n c (x₀ y) := by
  have h0 : atNL E (n' + c') n' (Loc.inX E n' c' y) = 0 := by
    unfold atNL
    split_ifs with h
    · simp [Loc.inX]
    · rfl
  simp [joinCol, proj_inX, h0]

theorem joinCol_add {n' c' n c : ℕ} (x₀ z : HomE E n' n) (t : E) (y' : Sp E n) :
    (joinCol (x₀ + t • z) y' : HomE E (n' + c') (n + c)) =
      joinCol x₀ y' + t • (Loc.inX E n c ∘ₗ z ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  refine LinearMap.ext fun v => ?_
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smul]
  abel

theorem locSmall_joinCol {P : HeightOneSpectrum (𝓞 E)} {q n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {Φ : HomE E (n' + c') (n + c) → K} {β : ℝ}
    (h : LocSmall q (LocE.lamY P q n' c' ex') (LocE.lamY P q n c ex) Φ β) (y' : Sp E n) :
    LocSmall q (stdAt E n' P) (stdAt E n P) (fun x₀ => Φ (joinCol x₀ y')) β := by
  refine ⟨fun x hx y hy => ?_, fun x z hz => ?_, fun σ x => h.2.2 σ _⟩
  · have := h.1 _ hx _ ((inX_mem_iff P q n' c' ex' y).2 hy)
    rw [joinCol_inX] at this
    exact (inX_mem_iff P q n c ex _).1 this
  · show Φ (joinCol (x + (q : E) • z) y') = Φ (joinCol x y')
    rw [joinCol_add]
    exact h.2.1 _ _ fun v hv => (inX_mem_iff P q n c ex _).2 (hz _ (proj_mem hv))

theorem smallDatum_of_frames {a b : ℕ} {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} [DecidableEq (HeightOneSpectrum (𝓞 E))]
    (d : Deco E a ST SG) (d' : DecoSet (E := E) (n := b) (ST := ST) (SG := SG'))
    (f : Frs E a SB) (f' : Frs E b SB) (hf : ∀ (P : SB) x, f P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1)
    (hf' : ∀ (P : SB) x, f' P x ∈ d'.1.at P.1 ↔ x ∈ stdAt E b P.1) (c : ℕ) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (hT : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (Ψ : SB → HomE E a b → K) (β : SB → ℝ)
    (hΨ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Ψ P) (β P)) :
    SmallDatum (ST ∪ SB) d.N d'.1.N c (fun x => phiT K d d'.1 x * ∏ P : SB, Ψ P (inFr (f P) (f' P) x)) (∏ P, β P) := by
  refine ⟨fun x hx P hP y hy => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rcases Finset.mem_union.1 hP with hP | hP
    · unfold phiT at h1
      split_ifs at h1 with h
      · exact (h ⟨P, hP⟩ y hy).1
      · exact absurd rfl h1
    · have h3 := Finset.prod_ne_zero_iff.1 h2 ⟨P, hP⟩ (Finset.mem_univ _)
      have h4 : (f ⟨P, hP⟩).symm y ∈ stdAt E a P := (hf ⟨P, hP⟩ _).1 (by simpa using hy)
      have h5 := (hf' ⟨P, hP⟩ _).2 ((hΨ ⟨P, hP⟩).1 _ h3 _ h4)
      simpa [inFr] using h5
  · obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    have hz' : ∀ P ∈ ST ∪ SB, ∀ y ∈ d.at P, z y ∈ d'.1.at P := hz
    have e0 : (((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z) = (c : 𝓞 E) • z := rfl
    rw [e0]
    show phiT K d d'.1 _ * _ = phiT K d d'.1 _ * _
    congr 1
    · unfold phiT
      classical
      refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun P => forall_congr' fun y => forall_congr' fun hy => ?_) rfl rfl
      have hzy : z y ∈ d'.1.at P.1 := hz' P.1 (Finset.mem_union_left _ P.2) y hy
      have hc : (c : 𝓞 E) • z y ∈ d'.1.at P.1 := Submodule.smul_mem _ _ hzy
      have e : (x + (c : 𝓞 E) • z) y = x y + (c : 𝓞 E) • z y := rfl
      rw [e, Submodule.add_mem_iff_left _ hc]
      refine and_congr_right fun hx => ?_
      rw [d'.2.f_add P _ hx _ hc, d'.2.f_smul P _ _ hzy, Ideal.Quotient.eq_zero_iff_mem.2 (hT P.1 P.2), zero_mul, add_zero]
    · refine Finset.prod_congr rfl fun P _ => ?_
      obtain ⟨k, hk⟩ := hq P
      have e : inFr (f P) (f' P) (x + (c : 𝓞 E) • z) =
          inFr (f P) (f' P) x + (q P : E) • inFr (f P) (f' P) (k • z) := by
        refine LinearMap.ext fun v => ?_
        have : (c : 𝓞 E) • z = (q P : E) • (k • z) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hk, mul_smul]
        rw [this]
        simp [inFr]
      rw [e]
      refine (hΨ P).2.1 _ _ fun v hv => (hf' P _).1 ?_
      have := nsmul_mem (hz' P.1 (Finset.mem_union_right _ P.2) _ ((hf P v).2 hv)) k
      simpa [inFr] using this
  · show ‖σ (phiT K d d'.1 x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ‖σ (phiT K d d'.1 x)‖ ≤ 1 := by
      unfold phiT
      split_ifs <;> simp
    have h2 : ∏ P : SB, ‖σ (Ψ P (inFr (f P) (f' P) x))‖ ≤ ∏ P, β P :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => (hΨ P).2.2 σ _
    calc _ ≤ 1 * ∏ P, β P := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = _ := one_mul _

end Generic

end GlobalTheory.ColNorms.DatOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumMetricEqGramAtInfinitePlace
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
open Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ClassSumCoord

theorem ipAt_eq_gram : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (T : Formalism.L2.Col.GSD K) (h : T.Ok), T.Rat → ∀ (v : InfinitePlace K) (φ : T.EqFun), T.ipAt h v φ.1 φ.1 = star (fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) ⬝ᵥ ((T.toCSD h).H.map v.embedding *ᵥ fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) := by
  intro K _ _ _ T h R v φ
  letI := h.fintypeCl
  have hRc : (T.toCSD h).Rat := T.toCSDOf_rat h R T.outSec
  have hb := csd_hasRatBasis _ hRc
  have e : GlobalTheory.PeriodClassSum.coordAt T v φ.1 = GlobalTheory.PeriodOnStep.coAt (T.toCSD h) v (T.res h φ).1 := rfl
  rw [GlobalTheory.PeriodClassSum.ipAt_eq, e, GlobalTheory.PeriodOnStep.H_map _ v hb, GlobalTheory.PeriodOnStep.wForm_sum,
    GlobalTheory.PeriodOnStep.coAt_sum (T.toCSD h) v (T.res h φ)]
  simp only [Basis.equivFun_apply]
  rfl

end GlobalTheory.ClassSumCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOne
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem weil_unit_phase_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  intro F E _ _ _ _ _ _ σ h emb q hq hq2 ht u hu
  have hr := _root_.GlobalTheory.UnitReal.unit_real_of_congr_one E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  obtain ⟨hF, hE, h2, -⟩ := h
  let f : InfinitePlace F → InfinitePlace E := fun w => InfinitePlace.mk (emb w).1
  have hcomap : ∀ w, (f w).comap (algebraMap F E) = w := by
    intro w
    simp only [f]
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : Function.Injective f := fun a b hab => by
    rw [← hcomap a, ← hcomap b, hab]
  have hcard : Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
    have a1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have a2 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have b1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have b2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have c1 := IsTotallyReal.nrComplexPlaces_eq_zero F
    have c2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have d := Module.finrank_mul_finrank ℚ F E
    rw [h2] at d
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hfac : ∀ w, (emb w).1 ((u : 𝓞 E) : E) = (f w).embedding ((u : 𝓞 E) : E) := by
    intro w
    rcases InfinitePlace.embedding_mk_eq (emb w).1 with h' | h'
    · simp only [f]; rw [h']
    · simp only [f]; rw [h', ComplexEmbedding.conjugate_coe_eq, hr]
  rw [← hs]
  rw [← Fintype.prod_bijective f hbij (fun w => ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun v => (v.embedding ((u : 𝓞 E) : E) / ((‖v.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun w => by rw [hfac w])]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatFramedOfGramPosDef
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem datFramed_of_gram_posDef {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok)
    (hG : ∀ v : InfinitePlace K, (S.gramV.map v.embedding).PosDef) : DatFramed S h := by
  refine ⟨S.hDim h, (S.hB h).equivFun.symm, fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v),
    fun v => (frameOfSpec _ _ (GlobalTheory.PeriodClassSum.gramAt_posDef S h v (hG v))).1, fun v x => ?_⟩
  have h1 := (GlobalTheory.PeriodClassSum.isFormsOf_formsLat S h hG ⊥).2 v ((S.hB h).equivFun.symm x)
  have h2 : Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (S.hDim h))) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v x =
      Formalism.HermitianLatticesTheory.normAt (S.hB h) (fun v => frameOf (GlobalTheory.PeriodClassSum.gramAt S h v)) v ((S.hB h).equivFun.symm x) := by
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    congr 2
    unfold Formalism.HermitianLatticesTheory.vecAt
    funext i
    simp only [Pi.basisFun_repr, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [h2]
  exact h1

theorem evGSD_datFramed : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (P : LevFam X.E X.K R.r Pr.vGs) (u : Pr.Word) (h : (evGSD W Ch sel mu P u).Ok), DatFramed (evGSD W Ch sel mu P u) h := by
  intro X _ Pr R W Ch sel Sg mu P u h
  refine datFramed_of_gram_posDef _ h fun v => ?_
  have e : (evGSD W Ch sel mu P u).gramV = GlobalTheory.TestLat.Compare.gramB X.K (W.lamTrue u R.m) := by
    ext i k
    show pairVr X.emb (W.lamTrue u R.m) 1 (bVV _ _ i) (bVV _ _ k) = _
    rw [GlobalTheory.ColNorms.pairVr_one_eq]
    exact GlobalTheory.PeriodClassSum.pairK_one_basis (W.lamTrue u R.m) i k
  rw [e]
  exact GlobalTheory.PeriodClassSum.gramB_posDef (W.lamTrue u R.m) v.embedding

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.TwistIdeal

theorem htMap_le {K V W ι κ : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Module.Basis κ K W}
    {X' : InfinitePlace K → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K →+* ℂ) → W → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (hN : ∀ σ x, N' σ (φ x) ≤ t σ * N σ x) :
    Formalism.HN.htMap b X b' X' φ ≤ 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) := by
  have hop : ∀ v : InfinitePlace K, Formalism.HN.opNormAt b X b' X' v φ ^ 2 ≤ t v.embedding ^ 2 := fun v =>
    opNormAt_sq_le b X b' X' (fun v => (hG v).1) v (IsTotallyComplex.isComplex v) φ _ (sq_nonneg _) fun x => by
      rw [← normAt_sq_eq_majAt, ← normAt_sq_eq_majAt, (hG v).2, (hG' v).2, ← mul_pow]
      exact pow_le_pow_left₀ (normAt_nonneg _ _ _ _ |>.trans_eq ((hG' v).2 _)) (hN _ _) 2
  have hpos : ∀ v : InfinitePlace K, 0 < Formalism.HN.opNormAt b X b' X' v φ := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1) v φ hφ
  have hs : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K fun v => Real.log (t v.embedding)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e, htc σ]
  have hd : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K fun _ => (1 : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Embeddings.card] at this
    rw [this]; rfl
  have hn : (0 : ℝ) < Formalism.HN.nPl K := by
    have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    linarith
  unfold Formalism.HN.htMap
  rw [hs, hd]
  have hsum : ∑ v, Real.log (Formalism.HN.opNormAt b X b' X' v φ ^ 2) ≤ ∑ v : InfinitePlace K, 2 * Real.log (t v.embedding) :=
    Finset.sum_le_sum fun v _ => by
      have := Real.log_le_log (pow_pos (hpos v) 2) (hop v)
      rw [Real.log_pow, Real.log_pow] at this
      rw [Real.log_pow]
      push_cast at this ⊢
      exact this
  rw [← Finset.mul_sum] at hsum
  rw [one_div, inv_mul_le_iff₀ hn]
  have : 2 * (2 * ∑ v : InfinitePlace K, Real.log (t v.embedding)) / (2 * (Formalism.HN.nPl K : ℝ)) * Formalism.HN.nPl K =
      2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    field_simp
  linarith

end GlobalTheory.TwistIdeal

namespace GlobalTheory.TwistIdeal

theorem deg_add_le_deg_of_ideal_smul_le : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N N' φ t L L' 𝔞 hN hN' hinj htpos htc hNb hL hL' h𝔞 hsub hrk
  by_cases h0 : L = ⊥
  · subst h0
    have h1 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by simp [Formalism.HN.rkK]
    rw [h1] at hrk
    simp [deg, h1, hrk]
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hI : ((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsm : Formalism.HermitianLatticesTheory.idealSmul (((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K)
      (L.map (φ.restrictScalars (𝓞 K))) ≤ L' := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (S := (nonZeroDivisors (𝓞 K))) (P := K)).1 ha
    rw [algebraMap_smul]
    exact hsub (Submodule.smul_mem_smul hr hx)
  have key := Formalism.ExtensionFiltration.twistLower K V (Fin n) W (Fin n') b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1)
    φ L L' (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) hI hL hL' h0 hinj hsm hrk
  have hφ : φ ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact hx0 (hinj (by rw [h, map_zero, LinearMap.zero_apply]))
  have hht := htMap_le hG hG' φ hφ t htpos htc hNb
  rw [FractionalIdeal.coeIdeal_absNorm] at key
  have hb : slope_sq N L / 2 - (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ slope_sq N' L' / 2 := by
    rw [slope_sq_eq hG hL, slope_sq_eq hG' hL']
    have e1 : 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) =
        2 * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by ring
    have e2 : 2 * Real.log ((Ideal.absNorm 𝔞 : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        2 * (Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) := by push_cast; ring
    rw [e1] at hht
    rw [e2] at key
    linarith
  have hr : (0 : ℝ) ≤ Formalism.HN.rkK L := Nat.cast_nonneg _
  unfold deg GlobalTheory.AllWt.slope
  rw [hrk]
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

end GlobalTheory.TwistIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegScale
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.NormScale

theorem deg_scale : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N N' : (K →+* ℂ) → V → ℝ) (t : (K →+* ℂ) → ℝ), HasGram N → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ x = t σ * N σ x) → HasGram N' ∧ ∀ L : Submodule (𝓞 K) V, L.FG → deg N' L = deg N L - (Formalism.HN.rkK L : ℝ) * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ N N' t hN ht hc hN'
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  set X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => ((t v.embedding : ℂ)⁻¹) • X v with hX'
  have htc : ∀ v : InfinitePlace K, (t v.embedding : ℂ) ≠ 0 := fun v => by
    exact_mod_cast (ht v.embedding).ne'
  have hinv : ∀ v, (X' v)⁻¹ = (t v.embedding : ℂ) • (X v)⁻¹ := fun v => by
    refine Matrix.inv_eq_left_inv ?_
    simp only [hX', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hG v).1,
      inv_mul_cancel₀ (htc v), one_smul]
  have hfc : ∀ v x, Formalism.HermitianLatticesTheory.fcoord b X' v x = (t v.embedding : ℂ) • Formalism.HermitianLatticesTheory.fcoord b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.fcoord, hinv]
    exact Matrix.smul_mulVec _ _ _
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt b X' v x = t v.embedding * Formalism.HermitianLatticesTheory.normAt b X v x := fun v x => by
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, hfc, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
      ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht _)]
  have hG' : IsGram b X' N' := fun v => by
    refine ⟨?_, fun x => by rw [hnorm, (hG v).2, hN']⟩
    simp only [hX', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero (htc v)))).mul (hG v).1
  refine ⟨hG'.hasGram, fun L hL => ?_⟩
  have hgram : ∀ v {j : ℕ} (e : Fin j → V), Formalism.HN.gramPl b X' v e = (((t v.embedding) ^ 2 : ℝ) : ℂ) • Formalism.HN.gramPl b X v e := by
    intro v j e
    ext a c
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hfc, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  have hdet : ∀ v {j : ℕ} (e : Fin j → V), (Formalism.HN.gramPl b X' v e).det.re =
      t v.embedding ^ (2 * j) * (Formalism.HN.gramPl b X v e).det.re := by
    intro v j e
    rw [hgram, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul, ← pow_mul]
  haveI : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = Module.finrank K (Submodule.span K (L : Set V)) := rfl
  generalize Module.finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  obtain ⟨-, g1, m1⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  obtain ⟨-, g2, m2⟩ := GlobalTheory.SlopeExt.rk_mul_mu_eq b X' (fun v => (hG' v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hlog : ∀ v, Real.log (Formalism.HN.gramPl b X' v e).det.re =
      (2 * j : ℝ) * Real.log (t v.embedding) + Real.log (Formalism.HN.gramPl b X v e).det.re := fun v => by
    rw [hdet, Real.log_mul (pow_pos (ht _) _).ne' (g1 v).ne', Real.log_pow]
    push_cast; ring
  have hsum : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K (fun v => Real.log (t v.embedding))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]; exact congrArg Real.log (hc σ).symm
  have hfin : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    rw [← NumberField.Embeddings.card K ℂ, this]
    rfl
  have hP : (Formalism.HN.nPl K : ℝ) ≠ 0 := by exact_mod_cast Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero
  rw [Finset.sum_congr rfl (fun v _ => hlog v), Finset.sum_add_distrib, ← Finset.mul_sum] at m2
  simp only [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, slope_sq_eq hG hL, slope_sq_eq hG' hL, hj, hsum, hfin]
  have key : (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X' L) = (Formalism.HN.nPl K : ℝ) * ((j : ℝ) * Formalism.HN.muDef b X L)
      - 2 * j * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by linarith
  field_simp
  linear_combination key

end GlobalTheory.NormScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

theorem exists_rational_middle_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K], DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x)) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : K ⊗[F] E, t * sigR K σ t + inclR K (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z)) = 0) := by
  intro F E _ _ _ _ _ σ hσ K _ _ _ hd M J hM hJ hu x y hx hy
  obtain ⟨w, h1, h2⟩ := _root_.GlobalTheory.PlaneNorm.exists_local_unitNorm_vector F E σ hσ K M J hM hJ hu x y hx hy
  obtain ⟨z, hz, n1, n2⟩ := _root_.GlobalTheory.PlaneNormApprox.approx F E σ hσ K hd M J hJ x y hx w h1 h2
  exact ⟨z, hz, _root_.GlobalTheory.PlaneNormReduce.reduce F E σ hσ K M J hJ x z hx n1, _root_.GlobalTheory.PlaneNormReduce.reduce F E σ hσ K M J hJ z y hz n2⟩

end GlobalTheory.PlaneNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIdempotentMulLevelProjMulGoodPartEq
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

namespace GlobalTheory.GoodPartLevelForms

theorem lvlE_lvlPr_vE : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlPr B.r ℓ.P ℓ.ψ * B.vE ℓ = B.vE ℓ := by
  intro K _ _ _ G _ _ Pl0 B ℓ v0 s h
  exact Formalism.L2.DIV.BlockDat.lf_lvl_vE h

end GlobalTheory.GoodPartLevelForms
end

