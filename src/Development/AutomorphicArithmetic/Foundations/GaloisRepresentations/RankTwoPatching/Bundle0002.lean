module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.PsForm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.NormEqOneOfValuationEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005
public import Mathlib
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioT
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter ValuativeRel

namespace UpperTheory.Gal.SV.GlobalSectionsBijection

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ord_unif : GlobalTheory.SmGL.ord k (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) = 1 := by
  have hs := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.polFacts k).1
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact ord_eq_one (le_antisymm (le_uniformizer_iff.2 hs.1) (hp ▸ hs.2 p (hp ▸ uniformizer_lt_one)))

private theorem norm_neg_one (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) {x : kˣ} (hx : GlobalTheory.SmGL.ord k x = -1) :
    ‖((ξ x : ℂˣ) : ℂ)‖ = ‖((ξ (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) : ℂˣ) : ℂ)‖⁻¹ := by
  have hu : GlobalTheory.SmGL.ord k (x * UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) = 0 := by
    rw [ord_mul, hx, ord_unif]
    simp
  have h1 := PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one ξ hξ (ord_eq_zero_iff.1 hu)
  rw [map_mul, Units.val_mul, norm_mul] at h1
  exact eq_inv_of_mul_eq_one_left h1

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem eig_sum {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i)) (s : ℝ)
    {φ : ↥(Weil h)} (hφ : deg φ = 1) {α : ℂ}
    (hα : α ∈ ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).lpTw s).eig φ) :
    ∃ i, α = ((c i φ : ℂˣ) : ℂ) * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) := by
  rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ s, Multiset.mem_map] at hα
  obtain ⟨y, hy, rfl⟩ := hα
  have h1 : ∀ i, (WD.lpOfChar h (c i) (hc i)).charPol φ = X - C ((c i φ : ℂˣ) : ℂ) := fun i => by
    rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have h2 := Polynomial.isRoot_of_mem_roots hy
  rw [GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn] at h2
  have h3 : (List.ofFn ((fun y : WD h => y.charPol φ) ∘ fun i => WD.lpOfChar h (c i) (hc i))).prod =
      ∏ i, (X - C ((c i φ : ℂˣ) : ℂ)) := by
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => h1 i
  rw [h3, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, -, hi⟩ := h2
  refine ⟨i, ?_⟩
  simp only [eval_sub, eval_X, eval_C] at hi
  rw [sub_eq_zero.1 hi]

end WD

end UpperTheory.Gal.SV.GlobalSectionsBijection

open UpperTheory.Gal.SV.GlobalSectionsBijection in
theorem UpperTheory.Gal.SV.ratioT :
    UpperTheory.Gal.SV.RatioT := by
  intro K Ω _ _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n π t hw σ hσ φ hφ α hα β hβ
  have hP := (UpperTheory.V.Z.Win.plainRec K Ω A w h rc ⟨a, ha, L⟩ n π t hw σ hσ).1
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  have hA := psForm L σ ξ hξ hs' hu
  rw [hA] at hα hβ
  obtain ⟨i, rfl⟩ := eig_sum _ _ _ hφ hα
  obtain ⟨j, rfl⟩ := eig_sum _ _ _ hφ hβ
  have hq : ((normV w : ℕ) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV w
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion K) (a φ) = -1 := by rw [ha.ord_eq φ, hφ]
  have hwin : ∀ m, ((normV w : ℕ) : ℝ) ^ (t - 1 / 2) < ‖((ξ m (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ ∧
      ‖((ξ m (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ < ((normV w : ℕ) : ℝ) ^ (t + 1 / 2) := fun m => by
    rw [hq]
    exact hw.2 _ ⟨σ, hσ, hs'⟩ (ξ m) ⟨hξ m, Multiset.mem_map_of_mem _ (Finset.mem_univ_val m)⟩
  have hbi := (Real.rpow_pos_of_pos (by linarith) _).trans (hwin i).1
  have hbj := (Real.rpow_pos_of_pos (by linarith) _).trans (hwin j).1
  have hlt : ‖((ξ j (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ <
      ‖((ξ i (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ * ((normV w : ℕ) : ℝ) := by
    have e : ((normV w : ℕ) : ℝ) ^ (t + 1 / 2) = ((normV w : ℕ) : ℝ) ^ (t - 1 / 2) * ((normV w : ℕ) : ℝ) := by
      rw [← Real.rpow_add_one (by linarith)]
      congr 1
      ring
    calc _ < _ := (hwin j).2
      _ = _ := e
      _ < _ := mul_lt_mul_of_pos_right (hwin i).1 (by linarith)
  have hc : 0 < ‖((normV w : ℕ) : ℂ) ^ ((((1 - (n : ℝ)) / 2 : ℝ)) : ℂ)‖ := by
    refine norm_pos_iff.2 ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro e
    have : ((normV w : ℕ) : ℝ) = 0 := by exact_mod_cast e.1
    linarith
  simp only [MonoidHom.comp_apply]
  rw [norm_mul, norm_mul, norm_neg_one _ (hξ i) hord, norm_neg_one _ (hξ j) hord, ← mul_assoc]
  refine mul_lt_mul_of_pos_right ?_ hc
  rw [← div_eq_mul_inv, lt_div_iff₀ hbj, inv_mul_lt_iff₀ hbi]
  exact hlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.UnrAtOfIsoTwist
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace UpperTheory.Gal.SV

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem sat_equiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    {α : Fin n → ℂˣ} (φ : π.Equiv σ) (h : HasSatake π α) : HasSatake σ α := by
  refine ⟨GlobalTheory.Parabolic.isIrreducible_of_equiv φ h.1, ?_,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans h.2.2⟩
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h.2.1
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, fun g => ?_, fun e => h0 (φ.toLinearEquiv.injective (by simpa using e))⟩
  have e : φ (π g v) = σ g (φ v) := φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [← e, hv g, map_smul]

theorem hasSatake_of {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧ HasSatake σ.ρ α := by
  obtain ⟨l, rfl⟩ := Quot.exists_rep B
  have hl : l.length = n := by simpa using hB.card
  subst hl
  have e : (Quot.mk _ l : Multiset ℂˣ) = Finset.univ.val.map l.get := by
    rw [Fin.univ_val_map, List.ofFn_get]; rfl
  obtain ⟨x, hx⟩ := hB.exists_vec
  exact ⟨l.get, e, GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ _ (e ▸ hx)⟩

theorem rec_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  obtain ⟨α, e0, hα⟩ := hasSatake_of σ hB
  obtain ⟨a, ha, ε, L⟩ := extraV E Ω A w h rc H
  have q := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    L.sat (IrrGL.of σ.ρ σ.smooth σ.irred) α (sat_equiv q hα)
  refine ⟨α, e0, ?_⟩
  rw [algNorm, L.nu_eq, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

theorem frob_of {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G E Ω →* GL (Fin n) (Qbar l)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (H : ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc →
      IsWDOf ι r (rc (algNorm σ))) : FrobEig ι r w (algSat n (normV w) B) := by
  intro A h
  obtain ⟨rc, hrec⟩ := recTExists E Ω A w h
  obtain ⟨α, rfl, e⟩ := rec_diag hrec σ B hB
  have hx := H A h rc hrec
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [GlobalTheory.SatFrobLit.val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

theorem good_of_fixed {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n))) :
    Good (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ IsSpherical (IrrGL.of σ.ρ σ.smooth σ.irred).rep := by
  obtain ⟨B, hB⟩ := (_root_.GlobalTheory.RealGal.SatLocProof.main E n w σ).1 hf
  obtain ⟨α, -, hα⟩ := hasSatake_of σ hB
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have q := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have k := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (w.adicCompletion E) n (fun i => unrChar _ (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hα.2.2
  refine ⟨⟨_, HasSupport.of_equiv k q, fun y hy => Or.inl ?_⟩, (sat_equiv q hα).2.1⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  rfl


open GlobalTheory.RealGal.TwistUnr in
theorem unrAt_of_isoTwist (hA : AdmissibleReal) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (ha : 1 ≤ a)
    (π : TR.CuspSub F a) (η : HChar F) (hT : IsoTwist π η) (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ) (hB : π.HasSat u B) :
    η.UnrAt u := by
  have hL := _root_.GlobalTheory.RealGal.locCompR_of_admissibleReal hA
  obtain ⟨σ, hσ⟩ := (hL F a π u).1
  have hσ' := isLocComp_twist hT hσ
  obtain ⟨A, hAu⟩ := exists_isPlaceOver (AlgebraicClosure F) u
  obtain ⟨rc, H⟩ := recTExists F (AlgebraicClosure F) A u hAu
  obtain ⟨ar, har, ε, LL⟩ := extraV _ _ A u hAu rc H
  obtain ⟨g1, s1⟩ := good_of_fixed σ (hasFixed_of_hasSat hL hB hσ)
  have u1 := (LL.sph _).1 s1
  have u2 := (LL.sph _).1 (good_of_fixed _ (hasFixed_of_hasSat hL hB hσ')).2
  have hs := GlobalTheory.HeckeComp.smooth_loc η u
  have e : rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)))) =
      (rc (cls (ParLaws.toRep σ))).lpChar (rc (.ofChar (η.loc u) hs)) := by
    refine Eq.trans ?_ (LL.twist _ _ hs g1)
    exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm
  replace u2 : (rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u))))).unr := u2
  rw [e, LL.one] at u2
  have hd : 1 ≤ (rc (cls (ParLaws.toRep σ))).lpDim := by rw [LL.dim]; exact ha
  have hi := ine_trivial u1 hd _ u2
  have hU : (WD.lpOfChar hAu ((η.loc u).comp ar) (har.smooth hs)).unr := by
    rw [WD.lpOfChar, WD.unr_mk]
    refine ⟨rfl, fun s => LinearMap.ext fun v => funext fun i => ?_⟩
    have := hi s
    simp [this]
  have hU' := (GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff har hs).1 hU
  intro x hx
  refine hU' x ?_
  have h0 : Valued.v (x : u.adicCompletion F) ≠ 0 := by simp
  rw [← GlobalTheory.SmGL.ord_eq_zero_iff, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero]
  unfold IsUnitAt at hx
  rw [hx, WithZero.log_one]

end UpperTheory.Gal.SV

end
end

