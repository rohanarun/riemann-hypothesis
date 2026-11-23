module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem tate_nsmul_lev {p : ℕ} {M : Type} [CommGroup M]
    (s : _root_.GlobalTheory.HTLat.Tate p M) (k m : ℕ) :
    (k • s).lev m = s.lev m ^ k := by
  induction k with
  | zero => simp [_root_.GlobalTheory.HTLat.Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, _root_.GlobalTheory.HTLat.Tate.lev_add, ih, pow_succ]


open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AV.AbVar.tl_lev_surj_ker : ∀ (K : Type) [Field K]
    (l : ℕ) [Fact l.Prime] (A : _root_.GlobalTheory.AV.AbVar K) (n : ℕ),
    (∀ x : A.Pt, x ^ l ^ n = 1 →
        ∃ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = x) ∧
      ∀ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = 1 ↔
        ∃ s : _root_.GlobalTheory.AV.AbVar.Tl l A, t = (l : ℤ_[l]) ^ n • s := by
  intro K _ l hl A n
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  refine ⟨fun x hx => _root_.GlobalTheory.Published.tate_lev_surj l _
    (_root_.GlobalTheory.AV.AbVar.pt_divisible K A l hlpos) n x hx, fun t => ?_⟩
  have hcast : ∀ s : _root_.GlobalTheory.AV.AbVar.Tl l A,
      (l : ℤ_[l]) ^ n • s = (l ^ n : ℕ) • s := by
    intro s
    apply Subtype.ext
    funext m
    change ((l : ℤ_[l]) ^ n • s).lev m = ((l ^ n : ℕ) • s).lev m
    rw [_root_.GlobalTheory.HTLat.Tate.lev_smul, tate_nsmul_lev, ← Nat.cast_pow]
    exact _root_.GlobalTheory.PDiv.pow_digit_natCast (s.lev_pow m) (l ^ n)
  constructor
  · intro ht
    let u : ℕ → A.Pt := fun m => t.lev (m + n)
    have hu : ∀ m, u m ^ l ^ m = 1 ∧ u (m + 1) ^ l = u m := by
      intro m
      refine ⟨?_, ?_⟩
      · simp only [u]
        rw [Nat.add_comm, _root_.GlobalTheory.HTLat.Tate.lev_add_pow, ht]
      · simp only [u]
        rw [show m + 1 + n = m + n + 1 by omega, _root_.GlobalTheory.HTLat.Tate.lev_succ]
    refine ⟨_root_.GlobalTheory.HTLat.Tate.mk u hu, ?_⟩
    rw [hcast]
    apply Subtype.ext
    funext m
    change t.lev m = ((l ^ n : ℕ) • _root_.GlobalTheory.HTLat.Tate.mk u hu).lev m
    rw [tate_nsmul_lev,
      _root_.GlobalTheory.HTLat.Tate.lev_mk]
    simp only [u, _root_.GlobalTheory.HTLat.Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [hcast, tate_nsmul_lev, _root_.GlobalTheory.HTLat.Tate.lev_pow]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize.WtSize

theorem wtOf_abs_le {n : ℕ} {E : Finset ℚ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ E, |(x : ℝ)| ≤ B) (i : Fin n) :
    |(((wtOf n E).w i : ℤ) : ℝ)| ≤ B + n + 1 := by
  unfold wtOf
  split_ifs with h
  · show |((⌊GlobalTheory.SignedHC.highestWeight E h.1 i⌋ : ℤ) : ℝ)| ≤ _
    set y := GlobalTheory.SignedHC.highestWeight E h.1 i with hy
    have hy' : (y : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 i : ℝ) - (((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ)) := by
      rw [hy]; unfold GlobalTheory.SignedHC.highestWeight; push_cast; ring
    have hd := hB _ (GlobalTheory.SignedHC.descEnum_mem E h.1 i)
    have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := by positivity
    have f1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := by exact_mod_cast Int.floor_le y
    have f2 : (y : ℝ) < ⌊y⌋ + 1 := by exact_mod_cast Int.lt_floor_add_one y
    rw [abs_le] at hd ⊢
    constructor <;> linarith [hd.1, hd.2]
  · show |((((0 : Fin n → ℤ) i : ℤ)) : ℝ)| ≤ _
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
    linarith

end GlobalTheory.InfSize.WtSize

namespace GlobalTheory.InfSize.WtSize

theorem weightX_abs_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau) {x : ℚ}
    (hx : x ∈ (num D 1 τ).weightX D.R.m) : |(x : ℝ)| ≤ 5 * large₂.sc.b := by
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have hs' := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs'
  have hS := large₂.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have htN : D.R.t + 1 ≤ bigN D := by
    unfold bigN
    have := Nat.le_mul_of_pos_left (D.R.t + sLen D + 1) (by omega : 0 < D.R.m)
    omega
  have hsN : sLen D ≤ gap D 1 := by omega
  have hγ0 : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : (0 : ℝ) ≤ D.R.m := by positivity
  have htR : (D.R.t : ℝ) + 1 ≤ large₂.sc.b := by
    have h1 : ((D.R.t + 1 : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast htN.trans hNg
    push_cast at h1
    linarith
  have hsR : (sLen D : ℝ) ≤ large₂.sc.b := by
    have h1 : (sLen D : ℝ) ≤ gap D 1 := by exact_mod_cast hsN
    linarith
  have hmγ : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by positivity
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, hl1, hl2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have ev : (D.hc τ).v ⟨0, by omega⟩ = ((num D 1 τ).v 2 : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨0, by omega⟩
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨0, by omega⟩
    rw [ev] at v0 v1
    have ha : (num D 1 τ).a i = ((num D 1 τ).v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) := rfl
    have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v 2 : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v 2 : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    rw [ha]
    push_cast
    have p1 : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ0
    have p2 : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, hi2, hik, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hik' : i ≤ D.R.k := hik
    have ev : (D.hc τ).v ⟨i - 2, by omega⟩ = ((num D 1 τ).v (i - 2 + 2) : ℚ) :=
      (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).1 ⟨i - 2, by omega⟩
    rw [show i - 2 + 2 = i by omega] at ev
    obtain ⟨v0, v1⟩ := large₂.cloud_v τ ⟨i - 2, by omega⟩
    rw [ev] at v0 v1
    have v0' : (0 : ℝ) ≤ ((num D 1 τ).v i : ℝ) := by exact_mod_cast v0
    have v1' : ((num D 1 τ).v i : ℝ) ≤ large₂.Sc := by exact_mod_cast v1
    unfold GlobalTheory.SignedHC.GridData.vHalf
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hs τ hi1 hi2
    have ec : (num D 1 τ).cen i = cen D 1 τ i := rfl
    have es : (num D 1 τ).s = sLen D := rfl
    rw [ec, es]
    have hs1 : (((sLen D - 1 : ℕ)) : ℝ) ≤ large₂.sc.b := by
      have : ((sLen D - 1 : ℕ) : ℝ) ≤ sLen D := by exact_mod_cast Nat.sub_le _ _
      linarith
    have ha' : (a : ℝ) + 1 ≤ ((sLen D - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have c0' : (0 : ℝ) ≤ (cen D 1 τ i : ℝ) := by exact_mod_cast c0
    push_cast
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have hl2' : l ≤ D.R.m := hl2
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hs τ (j := l - 1) (by omega)
    rw [show l - 1 + 1 = l by omega] at e0 e1
    have et : (num D 1 τ).t = D.R.t := rfl
    rw [et]
    have ha' : (a : ℝ) + 1 ≤ (D.R.t : ℝ) + 1 := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have e0' : (0 : ℝ) ≤ ((num D 1 τ).e l : ℝ) := by exact_mod_cast e0
    push_cast
    rw [abs_le]; constructor <;> linarith

theorem wt_top_abs_le : ∃ K1 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), sc.cGap = 1 → ∀ τ i, |(((wt G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ K1 * large₂.sc.b := by
  refine ⟨7, fun D large₂ hs T L sc G hc τ i => ?_⟩
  obtain ⟨hγb, hb⟩ := GlobalTheory.BigTop.Fun.gap_le_b hs
  have h4 := (isLeast_gap D 1).1.2.1
  have hNg : bigN D ≤ gap D 1 := by
    have := Nat.le_self_pow (by norm_num : 3 ≠ 0) (bigN D)
    omega
  have hn := GlobalTheory.DefRank.rank_le_bigN G (.top D.R.m) (show D.R.m ≤ D.R.m from le_rfl)
  have hnb : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ large₂.sc.b := by
    have : (((G.V (.top D.R.m)).rank : ℕ) : ℝ) ≤ gap D 1 := by exact_mod_cast hn.trans hNg
    linarith
  have e : wt G (.top D.R.m) τ = wtOf (G.V (.top D.R.m)).rank ((num D 1 τ).weightX D.R.m) := by
    show wtOf _ (GlobalTheory.SignedHC.entries (Node.par D sc.cGap (.top D.R.m) τ)) = _
    rw [hc]
    exact congrArg _ (GlobalTheory.SignedHC.entries_plus _)
  rw [e]
  have := wtOf_abs_le (B := 5 * large₂.sc.b) (by linarith) (fun x hx => weightX_abs_le hs τ hx) i
  linarith

end GlobalTheory.InfSize.WtSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugate
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ThmARatio

open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host

theorem twisted_value {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (𝓞 E))} {χ ξ : HChar E}
    {Λ : ℂ → ℂ} {m : ℕ} (hU : UnramFin E) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q))
    (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hm : m ≠ 0) (hord : ξ.OrderDvd m) (htr : TrivOnF ξ) (htame : ∀ v, ξ.TameAt v)
    (hram : ∀ v, ξ.UnrAt v ↔ v ∉ Q) (hΛ : IsHeckeL (χ * ξ) Λ) :
    ∃ (ψc : PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) (T : (PicO (condQ 𝔣 (belowSet Q)) →* ℂˣ) → ℂ),
      (∀ y, finPart ξ y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 (belowSet Q)) χ ψ (T ψ)) ∧ Λ s = T ψc := by
  classical
  have hloc (a b : HChar E) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
      (a * b).loc v x = a.loc v x * b.loc v x := rfl
  have hp : ∀ x, ξ.1 x ^ m = 1 := fun x => by
    have := congrArg (fun c : HChar E => c.1 x) hord
    simpa using this
  have hχu : ∀ v ∈ belowSet Q, ∀ P, Over P v → χ.UnrAt P := fun v hv P hP => by
    have e := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
    rwa [expIn, multiplicity_eq_zero_of_not_dvd (hQ v hv).2, expAt_zero_iff] at e
  have hξu : ∀ v ∉ belowSet Q, ∀ P, Over P v → ξ.UnrAt P := fun v hv P hP =>
    (hram P).2 fun h => hv (Finset.mem_image.2 ⟨P, h, HeightOneSpectrum.ext hP⟩)
  have hv : IsValChar φ s κ 𝔣 (belowSet Q) (χ * ξ) := by
    refine ⟨hχ.1.mul (GlobalTheory.ToricDistribution.isUnitary_of_pow hm hp), hχ.2.1.mul htr, fun k => ?_,
      fun v P hP => ⟨fun hv => ?_, fun hv n => ?_⟩⟩
    · rw [HChar.inf_mul, GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one]
      exact hχ.2.2.1 k
    · intro x hx hx1
      rw [hloc, hχu v hv P hP x hx, htame P x hx hx1, one_mul]
    · rw [← (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v) n]
      refine forall_congr' fun x => forall_congr' fun hx => ?_
      rw [hloc, hξu v hv P hP x hx, mul_one]
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have hex : ∀ q : HeightOneSpectrum (OF E), ∃ P, q ∈ belowSet Q → P ∈ Q ∧ Over P q := fun q => by
    by_cases e : q ∈ belowSet Q
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 e
      exact ⟨P, fun _ => ⟨hP, over_below P⟩⟩
    · exact ⟨P₀, fun h => absurd h e⟩
  choose Pq hPq using hex
  have t := GlobalTheory.ToricDistributionObj.toricSumFormula_holds E I φ hφ s κ 𝔣 (belowSet Q) (χ * ξ) Pq Λ hU hs hb hQ hv
    (fun q hq => (hPq q hq).2) hΛ
  rw [Finset.filter_false_of_mem, Finset.prod_empty, mul_one] at t
  swap
  · intro q hq h
    refine (hram (Pq q)).1 (fun x hx => ?_) (hPq q hq).1
    have := h x hx
    rwa [hloc, hχu q hq _ (hPq q hq).2 x hx, one_mul] at this
  have hker : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ (finPart ξ).ker := by
    refine sup_le ?_ fun y hy => ?_
    · rintro _ ⟨k, rfl⟩
      have := finPart_mul_inf ξ k
      rwa [GlobalTheory.ToricDistribution.inf_of_pow hm hp, mul_one] at this
    · refine GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level htr (fun v => ?_) hy
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P _ => htame P⟩
        rw [pow_one]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
      · exact ⟨0, by rw [pow_zero]; exact one_dvd _, fun P hP => (ξ.unrAt_iff P).1 (hξu v hv P hP)⟩
  have hψ : ∀ y, finPart ξ y = QuotientGroup.lift _ (finPart ξ) hker (QuotientGroup.mk y) := fun _ => rfl
  obtain ⟨hfin, S, hS, hT⟩ := (isTwistedSum_iff_isToricSum hψ _).2 t
  exact ⟨_, fun ψ => ∑ᶠ q : PicO (condQ 𝔣 (belowSet Q)), ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0, hψ,
    fun ψ => ⟨hfin, S, hS, rfl⟩, hT⟩

theorem dvd_cond0 {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (v : HeightOneSpectrum (OF D.host.E))
    (h : v.asIdeal ∣ GlobalTheory.FunObj.SqNum.condF P) : v.asIdeal ∣ GlobalTheory.LamTie.cond0 D.host (P.w P.v0) := by
  obtain ⟨u, hu, hd⟩ := (v.prime.dvd_finsetProd_iff _).1 h
  have e : v = u := HeightOneSpectrum.ext
    (associated_iff_eq.1 ((v.irreducible.dvd_irreducible_iff_associated u.irreducible).1 (v.prime.dvd_of_dvd_pow hd)))
  subst e
  rcases P.mem_S0_of_sum_eq.1 hu with h0 | h1
  · have e : below (P.w P.v0) = v := (P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))).trans h0.symm
    unfold GlobalTheory.LamTie.cond0
    rw [e]
    exact dvd_mul_left _ _
  · refine Dvd.dvd.mul_right (Dvd.dvd.pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    push_cast
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1 with h | h | h | h
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h))
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h)
    · exact Ideal.mul_mem_left _ _ h

end GlobalTheory.ThmARatio

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivial
section
open scoped TensorProduct
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem keyLocal_of (h1 : KeyClosedPts) (h2 : KeyGeneric) : KeyLocal := by
  intro T O _ _ _ _ _ _ _ _ hA P _ φ hφ hsh hP _ q hq hu
  by_cases h : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h2 T O hA P φ hφ hsh hP h q hq hu
  · exact h1 T O hA P φ hφ hsh hP h q hq hu

theorem torsor_trivial : ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D],
    Module.Finite (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D → Module.Projective (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D → Module.FaithfullyFlat (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[(Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) D))
      (Pi.algHom (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[(Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))] (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) := by
  intro T O _ _ _ _ _ _ _ hA P _ φ hφ hsh q hq hu D _ _ hfin hproj hff act hbij
  have hO : KeyOrigin := GlobalTheory.T.torsor_trivial_strict_henselisation_origin
  have hAll : KeyAll :=
    GlobalTheory.T.torsorTrivialGenericFibre_of_strictHenselClosedFibre (keyLocal_of (GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre hO) (GlobalTheory.T.keyGeneric_of_keyClosedPts' (GlobalTheory.T.torsorTrivialClosedPoints_of_origin_closedFibre hO)))
  exact hAll T O hA P φ hφ hsh q hq hu D hfin hproj hff act hbij

end GlobalTheory.LocAcyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageThetaDictionaryExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageDict

theorem gBig_mono {P Q : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨CF1, h1⟩ := hP
  refine ⟨CF1, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF hCF
  exact ⟨C1, x1, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (g1 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem stage_dictionary : GBig fun {D} {T} {Lc} {sc} G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
        GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
        (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
          HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
        GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
        (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
        ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_mono GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b _ H W _ _ _ i j p q A A' WW X hX
  obtain ⟨FA, FA', FW, a, b, -, -, -, h⟩ := H W i j p q A A' WW X hX
  exact ⟨FA, FA', FW, a, b, h⟩

end GlobalTheory.StageDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_inverse_expansion_equivariant_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  first | exact @GlobalTheory.Mum.traitInv_eqv_value | exact GlobalTheory.Mum.traitInv_eqv_value | (intros; apply GlobalTheory.Mum.traitInv_eqv_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  first | exact @GlobalTheory.TInj.pull_unif_tors | exact GlobalTheory.TInj.pull_unif_tors | (intros; apply GlobalTheory.TInj.pull_unif_tors <;> assumption)
end

