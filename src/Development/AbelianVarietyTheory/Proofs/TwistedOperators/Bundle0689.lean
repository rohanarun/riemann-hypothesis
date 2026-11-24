module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisingTranslateCombination
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem biInv_eq_of_cells {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)]
    {R K : ∀ i, Subgroup (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι), BiInv R K l q → ∀ h h' : (∀ i, H i), (∀ i, i ∉ l → h i = h' i) →
      (∀ i ∈ l, ∃ r ∈ R i, ∃ k ∈ K i, h i = r * h' i * k) → q h = q h'
  | [], _, h, h', h1, _ => by
      have : h = h' := funext fun i => h1 i List.not_mem_nil
      rw [this]
  | i :: l, hq, h, h', h1, h2 => by
      have hi : i ∈ i :: l := List.mem_cons_self
      rcases h2 i hi with ⟨r, hr, k, hk, e⟩
      have hq' : BiInv R K l q := fun j hj => hq j (List.mem_cons_of_mem _ hj)
      set h₁ := Function.update h i (h' i) with hh₁
      have hi₁ : h₁ i = h' i := by simp [hh₁]
      have step1 : q h = q h₁ := by
        have a1 := (hq i List.mem_cons_self (Function.update h₁ i (h' i * k))).1 r hr
        have a2 := (hq i List.mem_cons_self h₁).2 k hk
        simp only [Function.update_self, Function.update_idem] at a1
        rw [hi₁] at a2
        have hh : h = Function.update h₁ i (r * (h' i * k)) := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [e, mul_assoc]
          · simp [hh₁, Function.update_of_ne hj]
        rw [hh, a1, a2]
      rw [step1]
      refine biInv_eq_of_cells l hq' h₁ h' (fun j hj => ?_) (fun j hj => ?_)
      · by_cases hji : j = i
        · subst hji; exact hi₁
        · rw [hh₁, Function.update_of_ne hji]
          exact h1 j (by simp [hji, hj])
      · by_cases hji : j = i
        · subst hji; exact ⟨1, one_mem _, 1, one_mem _, by simp [hi₁]⟩
        · rw [hh₁, Function.update_of_ne hji]
          exact h2 j (List.mem_cons_of_mem _ hj)

theorem zero_not_mem_idx (D : D7) : 0 ∉ idx D := by simp [idx, List.mem_range']; intro x _; omega

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R)

theorem evT_eq_zero_of (C : BiFam ch.G) (j : ℕ) (hj : Even j) (hjm : j < D.R.m) (hC : C j = 0) (f : SchRow ch.G)
    (u : ColPt ch.G) (y : RowPt ch.G) : evT C f u y = 0 := by
  obtain ⟨k, rfl⟩ := hj
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold evT
  rw [Finset.prod_eq_zero (i := k) (by simp [Finset.mem_range]; omega) (by rw [two_mul, hC]; rfl), zero_mul]

end
end GlobalTheory.RowVal

namespace GlobalTheory.RowVal
section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R)

theorem suppOn_of_cover (s : ℤˣ) (hC : CoverAt ch s) (hF : FlatAt ch s) (hO : OffAt ch) (hI : InvAt ch) (hT : TensAt ch)
    (hB : BasicAt ch) : SuppOn ch s := by
  intro t a τ hτ M hM P y b hb h h1 hne
  obtain ⟨hφ, hFt, hHaar, -, hGood, -, -⟩ := hB
  have hsum : ∀ h' : Pts ch.G, tot ch.W hM P τ (colFn ch a) (formTop ch t y) h' = ∑ d ∈ τ.support,
      τ d * per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h') d.1 P.1 (colFn ch a) (formTop ch t y) := fun _ => rfl
  have hne' := hne
  rw [hsum] at hne'
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  have hper := right_ne_zero_of_mul hdne
  have hnz : ∀ j, Even j → j < D.R.m → conAt ch.W hM (fockD ch.W t d.2 P.2) h j ≠ 0 := by
    intro j hj hjm h0
    apply hper
    have := hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) Unit {()} (fun _ => 1)
      (fun _ => conAt ch.W hM (fockD ch.W t d.2 P.2) h) (fun _ => d.1)
      (fun _ _ => hGood t _ τ hτ M hM d hd P.2 h)
      (fun u y' => by simp [evT_eq_zero_of ch _ j hj hjm h0]) P.1
    simpa using this
  have h0 : h 0 = 1 := h1 0 (zero_not_mem_idx D)
  obtain ⟨β, hβ⟩ := hC t b hb h (hO t _ τ hτ M hM d hd P.2 h h0 hnz)
  refine ⟨β, ?_, hβ⟩
  by_contra hns
  apply hne
  classical

  choose! r hr a' ha' k hk e using hβ
  let p : Pts ch.G := fun j => if j ∈ idx D then a' j else 1
  have hp : IsRealPt p := by
    refine ⟨fun j => ?_, fun j hj => by simp [p, hj]⟩
    by_cases hj : j ∈ idx D
    · simp only [p, if_pos hj]; exact ha' j hj
    · simp only [p, if_neg hj]; exact one_mem _
  have hmove : tot ch.W hM P τ (colFn ch a) (formTop ch t y) h = tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b β) := by
    refine biInv_eq_of_cells (idx D) (hI t a τ hτ M hM P y) h (p * b β) (fun j hj => ?_) (fun j hj => ?_)
    · simp [p, hj, h1 j hj, (hb β).1 j hj]
    · refine ⟨r j, hr j hj, k j, hk j hj, ?_⟩
      simp only [Pi.mul_apply, p, if_pos hj, e j hj, mul_assoc]
  rw [hmove]

  have hexp : ch.S.IsExpansion t (ch.Phi a) β 0 := by
    obtain ⟨e₀, he₀, -⟩ := hτ
    refine ⟨e₀, he₀, by simp, fun x y' _ _ => ?_⟩
    rw [Finsupp.sum_zero_index]
    simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall] at hns
    obtain ⟨w, hw⟩ := hns
    have hz : (ch.S.term t (ch.Phi a) β w).datum = 0 := by
      simpa [unfSupport, GridChoice.term] using hw
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hz]; rfl)
  obtain ⟨z, -, hFl⟩ := hF
  obtain ⟨Cr, -, hCr⟩ := hFl P.2 p hp
  obtain ⟨ζ, -, hz⟩ := hCr t (ch.Phi a) τ hτ M hM β (b β) (hb β) 0 (fun _ => 0) hexp (by intro d hd; simp at hd)
  rw [hsum]
  exact hT t M (hHaar t M hM) _ _ (hφ a) (hFt t y) _ τ.support (fun d => τ d)
    (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b β)) (fun d => d.1)
    (fun d hd => hGood t _ τ hτ M hM d hd P.2 _)
    (fun u y' => by simpa [Finsupp.sum] using hz u y') P.1

end

theorem big_suppOn_of_flat :
    GlobalTheory.RowClaim.Big fun ch => ∀ s, FlatAt ch s → OffAt ch → InvAt ch → TensAt ch → BasicAt ch → SuppOn ch s :=
  big_mono (fun ch hC s hF hO hI hT hB => suppOn_of_cover ch s (hC s) hF hO hI hT hB) _root_.GlobalTheory.RowVal.cover_at

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExpansionZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFlatAsm

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

theorem evT_combC_smul (c : Combs G) (a : ℕ → ℂ) (C C' : BiFam G) (h : ∀ j, Even j → j < D.R.m → C j = a j • C' j)
    (f : SchRow G) (u : ColPt G) (y : RowPt G) :
    evT (combC W c C) f u y = (∏ k ∈ Finset.range (D.R.m / 2), a (2 * k)) * evT (combC W c C') f u y := by
  simp only [evT]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k < D.R.m := by have := Finset.mem_range.1 hk; omega
  simp only [combC]
  rw [h _ (even_two_mul k) hk', GlobalTheory.SeeSaw.Scale.biComb_smul]
  rfl

theorem isRealFam_smul (a : ℕ → ℂ) {C : BiFam G} (h : IsRealFam W C) : IsRealFam W fun j => a j • C j :=
  fun j hj hm => ⟨GlobalTheory.SeeSaw.Scale.isBiVac_smul _ (h j hj hm).1, GlobalTheory.SeeSaw.Scale.isBiSmooth_smul _ (h j hj hm).2⟩

theorem prod_ite_zero (κ : ℂ) :
    ∏ k ∈ Finset.range (D.R.m / 2), (if 2 * k = 0 then κ else 1) = κ := by
  have hm : 0 ∈ Finset.range (D.R.m / 2) := by have := D.R.two_le_m; exact Finset.mem_range.2 (by omega)
  rw [Finset.prod_eq_single_of_mem 0 hm fun k _ hk => if_neg (by omega)]
  exact if_pos rfl


variable {W} in
theorem isExpansion_zero {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (hβ : β ∉ S.supp t Φ)
    {τ : PureDat G t →₀ ℂ} (h : S.IsExpansion t Φ β τ) : S.IsExpansion t Φ β 0 := by
  obtain ⟨e, he, -, -⟩ := h
  refine ⟨e, he, fun d hd => by simp at hd, fun x y _ _ => ?_⟩
  simp only [GridChoice.supp, Set.mem_setOf_eq, not_forall, unfSupport, not_not] at hβ
  obtain ⟨w, hw⟩ := hβ
  rw [Finsupp.sum_zero_index]
  refine (Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm
  simp only [GridChoice.term]
  rw [hw]
  rfl

end Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem flatAt_of (s : ℤˣ) (hl : LocAt ch s) (hv : VacAt ch) (ho : OneAt ch) : FlatAt ch s := by
  obtain ⟨κ, z₁, hz₁, hl⟩ := hl
  obtain ⟨hb, z₂, hz₂, hv⟩ := hv
  refine ⟨fun t => z₁ t * (∏ k ∈ Finset.range (D.R.m / 2), z₂ t (2 * k))⁻¹,
    fun t => mul_mem (hz₁ t) (inv_mem (prod_mem fun k _ => hz₂ t _)), fun P p hp => ?_⟩
  obtain ⟨C₀, hC₀, hC⟩ := hv P p hp
  refine ⟨fun j => (if j = 0 then κ else 1) • C₀ j, isRealFam_smul ch.W _ hC₀,
    fun t Φ τ hτ M hM β b hβ τ' c hτ' hc => ?_⟩
  obtain ⟨b₀, hb₀⟩ := hb t
  by_cases hs : Stair t β
  · refine ⟨_, fun _ => rfl, fun u y => ?_⟩
    obtain ⟨ζ, hζ, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ τ' c hτ' hc
    rw [e P p hp u y, hζ hs, Finsupp.mul_sum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [evT_combC_smul ch.W (c d) (fun j => (z₂ t j : ℂ)) _ C₀ (hC t M hM b₀ hb₀),
      evT_combC_smul ch.W (c d) (fun j => if j = 0 then κ else 1) _ C₀ (fun _ _ _ => rfl), prod_ite_zero]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_prod, _root_.mul_inv_rev, inv_inv]
    ring
  · refine ⟨0, fun h => absurd h hs, fun u y => ?_⟩
    obtain ⟨ζ, -, e⟩ := hl t Φ τ hτ M hM β b b₀ hβ hb₀ 0 c
      (isExpansion_zero _ t Φ β (fun h => hs (ho t Φ β h)) hτ') (fun d hd => by simp at hd)
    rw [e P p hp u y, Finsupp.sum_zero_index, mul_zero, zero_mul]

theorem flatAt_big : Big fun ch => ∃ s, FlatAt ch s :=
  big_mono (fun ch ⟨⟨⟨s, hl⟩, hv⟩, ho⟩ => ⟨s, flatAt_of ch s hl hv ho⟩) ((_root_.GlobalTheory.RowVal.exists_locAt_big.and _root_.GlobalTheory.RowVal.OneVac.big_vacAt).and _root_.GlobalTheory.RowVal.oneAt)

end GlobalTheory.RowFlatAsm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConst

theorem kerSmall_rat_mid {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, kerSmall W Θ' g g₁ (γ * u) = kerSmall W Θ' g g₁ u := by
  intro γ hγ u
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨h2, h1⟩ := GlobalTheory.SmallRoute.theta_of_matched hΘ hd
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (γ * u) g d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul]
    exact hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)

theorem setIntegral_mul_right {D : D7} (V : HSp D) (ν : Measure (GA D V)) [hH : ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (k : GA D V) :
    IntegrableOn (fun u => F (u * k)) fd ν ∧ ∫ u in fd, F (u * k) ∂ν = ∫ u in fd, F u ∂ν := by
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V ν hH
  have hmp : MeasurePreserving (fun x : GA D V => x * k⁻¹) ν ν := measurePreserving_mul_right ν k⁻¹
  have ht : IsFundamentalDomain (GQ V) ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν :=
    hfd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  have hinv : ∀ (g : GQ V) (x : GA D V), F (g • x) = F x := fun g x => hF g g.2 x
  have hmp2 : MeasurePreserving (fun x : GA D V => x * k) ν ν := measurePreserving_mul_right ν k
  have hpre : (fun x : GA D V => x * k) ⁻¹' ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) = fd := by
    ext x; simp
  have hemb : MeasurableEmbedding (fun x : GA D V => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have h1 : IntegrableOn F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν := (hfd.integrableOn_iff ht hinv).1 hint
  have e1 : ∫ u in fd, F (u * k) ∂ν = ∫ u in (fun x : GA D V => x * k⁻¹) ⁻¹' fd, F u ∂ν := by
    have := hmp2.setIntegral_preimage_emb hemb F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd)
    rw [hpre] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact (hmp2.integrableOn_comp_preimage hemb).2 h1
  · rw [e1]; exact (hfd.setIntegral_eq ht hinv).symm

theorem translates_left_inv {D : D7} {V : HSp D} (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (w : GA D V →₀ ℂ) : ∀ γ ∈ GQ V, ∀ u, translates w F (γ * u) = translates w F u := by
  intro γ hγ u
  unfold translates
  refine Finsupp.sum_congr fun k _ => ?_
  rw [mul_assoc, hF γ hγ]

theorem integral_translates {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (w : GA D V →₀ ℂ) :
    IntegrableOn (translates w F) fd ν ∧ ∫ u in fd, translates w F u ∂ν = zdeg w * ∫ u in fd, F u ∂ν := by
  have h := fun k => setIntegral_mul_right V ν fd hfd F hF hint k
  have e : translates w F = fun u => ∑ k ∈ w.support, w k * F (u * k) := by
    funext u; rfl
  rw [e]
  refine ⟨integrable_finsetSum _ fun k _ => (h k).1.const_mul _, ?_⟩
  rw [integral_finsetSum _ fun k _ => (h k).1.const_mul _]
  simp only [integral_const_mul, (h _).2]
  rw [zdeg, Finsupp.sum, Finset.sum_mul]

theorem translates_comm {H : Type} [Monoid H] (F : H → ℂ) (a b : H →₀ ℂ)
    (hab : ∀ x ∈ a.support, ∀ y ∈ b.support, x * y = y * x) :
    translates a (translates b F) = translates b (translates a F) := by
  funext u
  simp only [translates, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  rw [mul_assoc, mul_assoc, hab x hx y hy]; ring

theorem zdeg_mul_integral_comm {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (a b : GA D V →₀ ℂ) (hab : ∀ x ∈ a.support, ∀ y ∈ b.support, x * y = y * x)
    (ha : IntegrableOn (translates a F) fd ν) (hb : IntegrableOn (translates b F) fd ν) :
    zdeg a * ∫ u in fd, translates b F u ∂ν = zdeg b * ∫ u in fd, translates a F u ∂ν := by
  rw [← (integral_translates V ν fd hfd _ (translates_left_inv F hF b) hb a).2,
    ← (integral_translates V ν fd hfd _ (translates_left_inv F hF a) ha b).2, translates_comm F a b hab]

end GlobalTheory.SmallConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    ((∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0))) := by
  first | exact @GlobalTheory.ExpansionInvariance.levels_invariant | exact GlobalTheory.ExpansionInvariance.levels_invariant | (intros; apply GlobalTheory.ExpansionInvariance.levels_invariant <;> assumption)
end

