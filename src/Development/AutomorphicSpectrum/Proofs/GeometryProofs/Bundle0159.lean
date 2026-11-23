module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genericFibre_reduced_noetherian_closed : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  intro F _ _ P s hs hn
  have hp : IsProjOver (pullback.snd s (spMap (algebraMap (𝓞 F) F))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 F)) (S := F) (nonZeroDivisors (𝓞 F))
  have hbf : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap (𝓞 F) F)))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap (𝓞 F) F))), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap (𝓞 F) F))).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap (algebraMap (𝓞 F) F)) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

end GlobalTheory.CompanionTheory.Ar.SncBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrank
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue (exists_homog exists_homog_mem aeval_div)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono mem_mCoordIdeal_of_aeval_eq_zero)
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff mem_locRing_iff div_mem_locRing)

theorem length_toNat_of_addEquiv {M κ : Type*} [AddCommGroup M] [Module ℤ M] [Field κ] (e : M ≃+ κ)
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) κ] :
    (Module.length ℤ M).toNat = Module.finrank (ZMod p) κ := by
  let l : M ≃ₗ[ℤ] κ := { e with map_smul' := fun n x => by simpa using map_intCast_smul e ℤ ℤ n x }
  rw [l.length_eq, Module.length_eq_of_surjective (R := ZMod p) (S := ℤ) (M := κ)
    (fun z => ⟨(z.cast : ℤ), by simp⟩), Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

attribute [local instance 2000] Ring.toIntAlgebra

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {P W : Ideal (MRing J)} [P.IsPrime] [W.IsPrime]

def dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) : MRing J →+* locRing P W := by
  classical
  exact (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩),
      div_mem_locRing hPW (homog_X p.1 p.2) (homog_X p.1 (c p.1)) (hc p.1)⟩ : locRing P W)).toRingHom

theorem frac_chart_ne_zero (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    fracHom P (X ⟨k, c k⟩ : MRing J) ≠ 0 := fun h =>
  hc k (hPW (fracHom_eq_zero_iff.1 h))

theorem coe_dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (f : MRing J) :
    ((dehom hPW c hc f : locRing P W) : FractionRing (MRing J ⧸ P)) =
      aeval (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩)) f := by
  classical
  have h : (locRing P W).subtype.comp (dehom hPW c hc) =
      (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩))).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [dehom]
  exact RingHom.congr_fun h f

theorem fracHom_eq_aeval (f : MRing J) :
    fracHom P f = aeval (fun p : Σ k, J k => fracHom P (X p)) f := by
  have h : fracHom P = (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
  exact RingHom.congr_fun h f

theorem dehom_form (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) {G : MRing J} {n : B → ℕ}
    (hG : IsMultiHomog G n) :
    ((dehom hPW c hc G : locRing P W) : FractionRing (MRing J ⧸ P)) * fracHom P (chartMono c n) = fracHom P G := by
  have hD : fracHom P (chartMono c n) = ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k := by
    simp [chartMono, map_prod, map_pow]
  have hD0 : ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (frac_chart_ne_zero hPW hc k)
  rw [coe_dehom, aeval_div (fun p : Σ k, J k => fracHom P (X p)) c G n hG, hD, ← fracHom_eq_aeval,
    mul_assoc, inv_mul_cancel₀ hD0, mul_one]

theorem dehom_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    dehom hPW c hc (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  rw [coe_dehom, aeval_X]
  exact div_self (frac_chart_ne_zero hPW hc k)

variable [IsLocalRing (locRing P W)]

theorem dehom_mem_maximalIdeal_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) :
    dehom hPW c hc G ∈ maximalIdeal (locRing P W) ↔ G ∈ W :=
  regularityLocalFlat_holds.mem_maximalIdeal_iff hPW _ hG (isMultiHomog_chartMono c n)
    (chartMono_notMem ‹W.IsPrime› hc n) (dehom_form hPW hc hG)

def theta (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) :
    MRing J →+* ResidueField (locRing P W) :=
  (residue (locRing P W)).comp (dehom hPW c hc)

theorem theta_eq_zero_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) : theta hPW c hc G = 0 ↔ G ∈ W :=
  (residue_eq_zero_iff _).trans (dehom_mem_maximalIdeal_iff hPW hc hG)

theorem theta_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    theta hPW c hc (X ⟨k, c k⟩) = 1 := by
  simp [theta, dehom_X_chart]

theorem ker_theta (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hWh : IsMultiHomogIdeal W) :
    RingHom.ker (theta hPW c hc) = W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hIk : I0 ≤ RingHom.ker (theta hPW c hc) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp [SetLike.mem_coe, RingHom.mem_ker, theta_X_chart]
  apply le_antisymm
  · intro f hf
    have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨k, rfl⟩
    obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
    have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
    have hG0 : G ∈ RingHom.ker (theta hPW c hc) := by simpa using add_mem (hIk hd) hf
    have hGW : G ∈ W := (theta_eq_zero_iff hPW hc hG).1 hG0
    have e : f = G - (G - f) := by ring
    rw [e]
    exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)
  · refine sup_le ?_ hIk
    intro f hf
    obtain ⟨n, G, hGW, hG, e⟩ := exists_homog_mem (theta hPW c hc) c (theta_X_chart hPW hc) hWh hf
    rw [RingHom.mem_ker, ← e]
    exact (theta_eq_zero_iff hPW hc hG).2 hGW

theorem theta_surjective (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hmax : (RingHom.ker (theta hPW c hc)).IsMaximal) : Function.Surjective (theta hPW c hc) := by
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := (mem_locRing_iff hPW).1 x.2
  have hvk : v ∉ RingHom.ker (theta hPW c hc) := fun h => hvW ((theta_eq_zero_iff hPW hc hv).1 h)
  obtain ⟨g, i, hi, hgi⟩ := hmax.exists_inv hvk
  have hD0 : fracHom P (chartMono c a) ≠ 0 := fun h =>
    chartMono_notMem ‹W.IsPrime› hc a (hPW (fracHom_eq_zero_iff.1 h))
  have h1 : dehom hPW c hc u = x * dehom hPW c hc v := by
    apply Subtype.ext
    apply mul_right_cancel₀ hD0
    rw [dehom_form hPW hc hu, ← hx, Subring.coe_mul, mul_assoc, dehom_form hPW hc hv]
  have h2 : theta hPW c hc g * theta hPW c hc v = 1 := by
    have := congrArg (theta hPW c hc) hgi
    rwa [map_add, map_mul, RingHom.mem_ker.1 hi, add_zero, map_one] at this
  refine ⟨u * g, ?_⟩
  have h3 : theta hPW c hc u = residue _ x * theta hPW c hc v := by
    simp only [theta, RingHom.comp_apply, h1, map_mul]
  rw [map_mul, h3, mul_assoc, mul_comm (theta hPW c hc v), h2, mul_one]


omit [P.IsPrime] [W.IsPrime] in
def chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) : MRing J →+* chartRingZ w c :=
  (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨w p / w ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩ : chartRingZ w c)).toRingHom

theorem coe_chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) (f : MRing J) :
    ((chartHom w c f : chartRingZ w c) : K) = aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) f := by
  have h : (chartRingZ w c).val.toRingHom.comp (chartHom w c) =
      (aeval (R := ℤ) (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [chartHom]
  exact RingHom.congr_fun h f

theorem chartHom_surjective {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) :
    Function.Surjective (chartHom w c) := by
  rintro ⟨r, hr⟩
  rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hr
  exact ⟨f, Subtype.ext ((coe_chartHom w c f).trans hf)⟩

theorem ker_chartHom_le {K : Type} [Field K] {w : (Σ k, J k) → K} {c : ∀ k, J k} {W : Ideal (MRing J)}
    (hPW : mCoordIdeal w ≤ W) (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    RingHom.ker (chartHom w c) ≤ W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hspan : I0 ≤ RingHom.ker (chartHom w c) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    apply Subtype.ext
    rw [coe_chartHom]
    simp [hwc k]
  intro f hf
  have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨k, rfl⟩
  obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
  have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
  have hG0 : chartHom w c G = 0 := by simpa using add_mem (hspan hd) hf
  have hGv : aeval w G = 0 := by
    have h1 := congrArg Subtype.val hG0
    rw [coe_chartHom, aeval_div w c G n hG] at h1
    exact (mul_eq_zero.1 h1).resolve_right
      (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)))
  have hGW : G ∈ W := hPW (mem_mCoordIdeal_of_aeval_eq_zero w hG hGv)
  have e : f = G - (G - f) := by ring
  rw [e]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)

theorem ker_theta_isMaximal {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [IsFunctionField (ZMod p) K] {w : (Σ k, J k) → K} {W : Ideal (MRing J)} [(mCoordIdeal w).IsPrime] [W.IsPrime]
    [IsLocalRing (locRing (mCoordIdeal w) W)] (hbir : Birational w) (hPW : mCoordIdeal w ≤ W)
    {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (hWh : IsMultiHomogIdeal W)
    {k : B} {i : J k} (hw : w ⟨k, i⟩ ≠ 0) (hX : (X ⟨k, i⟩ : MRing J) ∈ W) :
    (RingHom.ker (theta hPW c hc)).IsMaximal := by
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k h => hc k (hPW ((X_mem_iff w k _).2 h))
  have hs := chartHom_surjective w c
  have hker := ker_theta hPW hc hWh
  have hle : RingHom.ker (chartHom w c) ≤ RingHom.ker (theta hPW c hc) := by
    rw [hker]
    exact ker_chartHom_le hPW hwc
  haveI : (RingHom.ker (theta hPW c hc)).IsPrime := RingHom.ker_isPrime _
  have hq : (Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc))).IsPrime :=
    Ideal.map_isPrime_of_surjective hs hle
  have h0 : Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)) ≠ ⊥ := by
    intro h
    have hx : (X ⟨k, i⟩ : MRing J) ∈ RingHom.ker (theta hPW c hc) := by
      rw [hker]
      exact Ideal.mem_sup_left hX
    have h1 := Ideal.mem_map_of_mem (chartHom w c) hx
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_chartHom, aeval_X] at h2
    exact div_ne_zero hw (hwc k) h2
  haveI := chart_prime_isMaximal (p := p) w hbir c hwc _ hq h0
  have h3 := Ideal.comap_isMaximal_of_surjective (chartHom w c) hs
    (K := Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)))
  have hle' : Ideal.comap (chartHom w c) ⊥ ≤ RingHom.ker (theta hPW c hc) := hle
  rwa [Ideal.comap_map_of_surjective (chartHom w c) hs, sup_eq_left.2 hle'] at h3

theorem geoNum_zero_eq_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  intro B _ J _ p _ K _ _ _ w hbir k i hw W hW b _ _
  classical
  obtain ⟨hmin, hrel⟩ := hW
  haveI hWp : W.IsPrime := hmin.1.1
  haveI hPp : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal w ≤ W := le_sup_left.trans hmin.1.2
  have hX : (X ⟨k, i⟩ : MRing J) ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hWh : IsMultiHomogIdeal W :=
    isMultiHomogIdeal_of_mem_minimalPrimes (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w)
      (homog_X k i) hmin
  have hc : ∀ k, (X ⟨k, (hrel k).choose⟩ : MRing J) ∉ W := fun k => (hrel k).choose_spec
  have hmax := ker_theta_isMaximal (p := p) hbir hPW hc hWh hw hX
  have hsurj := theta_surjective hPW hc hmax
  rw [geoNum, dite_eq_left hrel]
  congr 1
  exact length_toNat_of_addEquiv
    ((Ideal.quotEquivOfEq (ker_theta hPW hc hWh).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)).toAddEquiv p

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFromLocalMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
open GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L]

theorem gIdx_eq_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W)
    (h1 : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (h2 : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (h : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    gIdx A.toAddSubgroup B.toAddSubgroup = gIdx (locAt v A).toAddSubgroup (locAt v B).toAddSubgroup := by
  have eA : ∀ X Y : Submodule (𝓞 L) W, (X ⊓ Y).toAddSubgroup.relIndex X.toAddSubgroup =
      Y.toAddSubgroup.relIndex X.toAddSubgroup := fun X Y => by
    have : (X ⊓ Y).toAddSubgroup = Y.toAddSubgroup ⊓ X.toAddSubgroup := by
      ext x; simp [and_comm]
    rw [this, AddSubgroup.inf_relIndex_right]
  have hA : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w (A ⊓ B) := fun w hw => by
    rw [locAt_inf, ← h w hw, inf_idem]
  have hB : ∀ w : FinitePlace L, w ≠ v → locAt w B = locAt w (B ⊓ A) := fun w hw => by
    rw [locAt_inf, h w hw, inf_idem]
  have n1 := GlobalTheory.T.local_index_at_single_place L W v A (A ⊓ B) inf_le_left (by rwa [eA]) hA
  have n2 := GlobalTheory.T.local_index_at_single_place L W v B (B ⊓ A) inf_le_left (by rwa [eA]) hB
  rw [eA, locAt_inf, eA] at n1
  rw [eA, locAt_inf, eA] at n2
  rw [gIdx, gIdx, n1, n2]

variable {n : ℕ}

theorem gIdx_glued (S : Finset (FinitePlace L)) : ∀ T : FinitePlace L → Matrix (Fin n) (Fin n) L,
    (∀ v, (T v).det ≠ 0) → (∀ v, v ∉ S → UnitAt v (T v)) →
    gIdx (glued T).toAddSubgroup (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup =
      ∑ v ∈ S, Real.log (v (T v).det) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro T _ hS
    have : glued T = frame 1 := by
      rw [glued, ← iInf_locAt_frame_one]
      exact iInf_congr fun v => (hS v (by simp)).locAt_frame
    rw [this, gIdx_self, Finset.sum_empty]
  | insert v S hv ih =>
    intro T hd hS
    set T' := Function.update T v 1 with hT'
    have hTv : T' v = 1 := by simp [hT']
    have hTw : ∀ w, w ≠ v → T' w = T w := fun w hw => by simp [hT', hw]
    have hd' : ∀ w, (T' w).det ≠ 0 := fun w => by
      by_cases hw : w = v
      · subst hw; rw [hTv]; simp
      · rw [hTw w hw]; exact hd w
    have hS' : ∀ w, w ∉ S → UnitAt w (T' w) := fun w hw => by
      by_cases hwv : w = v
      · subst hwv; rw [hTv]; exact unitAt_one _
      · rw [hTw w hwv]; exact hS w (by simp [hwv, hw])
    have f1 : {w : FinitePlace L | ¬ UnitAt w (T w)}.Finite :=
      (Finset.finite_toSet (insert v S)).subset fun w hw => by
        by_contra h
        exact hw (hS w h)
    have f2 : {w : FinitePlace L | ¬ UnitAt w (T' w)}.Finite :=
      S.finite_toSet.subset fun w hw => by
        by_contra h
        exact hw (hS' w h)
    obtain ⟨a1, a2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T hd f1
    obtain ⟨b1, b2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T' hd' f2
    have c1 := AddSubgroup.relIndex_ne_zero_trans a1 b2
    have c2 := AddSubgroup.relIndex_ne_zero_trans b1 a2
    have loc : ∀ w : FinitePlace L, w ≠ v → locAt w (glued T) = locAt w (glued T') := fun w hw => by
      rw [GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2, hTw w hw]
    rw [gIdx_add c1 c2 b1 b2, gIdx_eq_locAt v _ _ c1 c2 loc, GlobalTheory.T.glued_lattice_localization L n T hd f1, GlobalTheory.T.glued_lattice_localization L n T' hd' f2,
      hTv, GlobalTheory.T.local_index_frame_log_det L n v (T v) (hd v), ih T' hd' hS', Finset.sum_insert hv]
    refine congrArg _ (Finset.sum_congr rfl fun w hw => ?_)
    rw [hTw w fun e => hv (e ▸ hw)]

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem logIdx_localFrames : ∀ (L : Type) [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (n : ℕ) (g : Fin n → V) (F : Submodule (𝓞 L) V) (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) L), LinearIndependent L g → (∀ v, (T v).det ≠ 0) → C.det ≠ 0 → {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite → (∀ x, x ∈ F ↔ x ∈ Submodule.span L (Set.range g) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • g j)) → logIdx F (fun k => ∑ j, C j k • g j) = (∑ᶠ v : FinitePlace L, Real.log (v (T v).det)) + ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ V _ _ _ _ n g F T C hg hd hC hfin hF
  classical

  let Φ : (Fin n → L) →ₗ[𝓞 L] V := (Fintype.linearCombination L g).restrictScalars (𝓞 L)
  have hΦ : Function.Injective Φ := hg.fintypeLinearCombination_injective
  have hΦa : ∀ c, Φ c = ∑ i, c i • g i := fun c => by
    simp [Φ, Fintype.linearCombination_apply]
  have hfr : ∀ A : Matrix (Fin n) (Fin n) L, (frame A).map Φ =
      Submodule.span (𝓞 L) (Set.range fun k => ∑ j, A j k • g j) := fun A => by
    rw [frame, Submodule.map_span, ← Set.range_comp]
    congr 2
  have hFg : F = (glued T).map Φ := by
    ext x
    rw [hF x, Submodule.mem_map]
    constructor
    · rintro ⟨hx, hl⟩
      have hr : x ∈ Set.range (Fintype.linearCombination L g) := by
        rw [← Fintype.range_linearCombination] at hx
        exact hx
      obtain ⟨c, rfl⟩ := hr
      refine ⟨c, ?_, rfl⟩
      rw [glued, Submodule.mem_iInf]
      intro v
      obtain ⟨t, ht, h⟩ := hl v
      rw [← hfr, Submodule.mem_map] at h
      obtain ⟨y, hy, e⟩ := h
      refine mem_locAt.2 ⟨t, ht, ?_⟩
      have : t • c = y := hΦ (by rw [map_smul, e]; rfl)
      rwa [this]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, fun v => ?_⟩
      · rw [← Fintype.range_linearCombination]
        exact ⟨c, rfl⟩
      · obtain ⟨t, ht, h⟩ := mem_locAt.1 ((Submodule.mem_iInf _).1 hc v)
        refine ⟨t, ht, ?_⟩
        rw [← hfr, ← map_smul]
        exact Submodule.mem_map_of_mem h
  have hidx : logIdx F (fun k => ∑ j, C j k • g j) = gIdx (glued T).toAddSubgroup (frame C).toAddSubgroup := by
    have e : logIdx F (fun k => ∑ j, C j k • g j) = gIdx F.toAddSubgroup ((frame C).map Φ).toAddSubgroup := by
      rw [hfr]; rfl
    rw [e, hFg, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact gIdx_map _ hΦ _ _
  obtain ⟨g1, g2, g3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame L n C hC
  have hfin' : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite := hfin
  obtain ⟨a1, a2⟩ := GlobalTheory.T.glued_lattice_finite_index L n T hd hfin'
  rw [hidx, gIdx_add a1 a2 g1 g2, g3, gIdx_glued hfin'.toFinset T hd fun v hv => by
    by_contra h
    exact hv (hfin'.mem_toFinset.2 h)]
  congr 1
  rw [finsum_eq_sum_of_support_subset]
  intro v hv
  rw [Set.Finite.coe_toFinset]
  intro h
  exact hv (show Real.log (v (T v).det) = 0 by rw [h.2, Real.log_one])

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFormOfIsHodgeGram
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem hodgeForm_of_isHodgeGram (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ)
    (v : Fin n → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (hL : L.IsLB) (hv : ∀ i, IsTanAt G x (v i))
    (h : Fl.IsHodgeGram G L x v Γ) (i j : Fin n) : HodgeForm G L x (v i) (v j) (Γ i j) := by
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := h
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨hL, hv i, hv j, Q.A, inferInstance, ψ, Q.g, GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u, Hm, χ, v' i, v' j,
    W i, W j, hp, GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH, (hvW i).1, (hvW j).1, (hvW i).2, (hvW j).2,
    hΓ i j⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliTwistAutomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem moduli_twist_phi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (g : HostAut H) (a : TwIso D g) (h : TwOK Xo.univ g a),
    ∃ Φ : Xo.X ⟶ Xo.X, Φ ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ) := by
  intro E _ _ _ H D l Xo g a h
  obtain ⟨f, ⟨hf, ho⟩, -⟩ :=
    Xo.rep Xo.X Xo.s (moduli_isReduced E H D l Xo) (twistObj Xo.univ g a h)
  exact ⟨f, hf, ho⟩

end GlobalTheory.CompanionTheory.Ar
end

