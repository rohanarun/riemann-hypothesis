module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPDelAtrEqLocPNabAtr
section
noncomputable section

namespace GlobalTheory.KerT

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker

theorem spread_lt_of_two_mul_lt {n p : ℕ} (hp : p.Prime) (lam : DomWeight n)
    (h : ∀ a b : Fin n, 2 * (lam.w a - lam.w b + (n : ℤ)) < (p : ℤ)) : lam.spread < p := by
  have hp0 := hp.pos
  unfold DomWeight.spread
  split_ifs with hn
  · have := h ⟨0, hn⟩ ⟨n - 1, by omega⟩
    omega
  · omega

theorem localization_delAtr_eq_localization_nabAtr : GlobalTheory.Published.InducedSimpleLowestAlcove →
    ∀ (X : Fields) (n p : ℕ) (lam : X.Tau → DomWeight n), p.Prime →
      (∀ τ (a b : Fin n), 2 * ((lam τ).w a - (lam τ).w b + (n : ℤ)) < (p : ℤ)) →
      ∀ w : HeightOneSpectrum (𝓞 X.K), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
        ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsFullLattice X.E L →
          localization₂ w.asIdeal (delAtr X.emb lam L) = localization₂ w.asIdeal (nabAtr X.emb lam L) := by
  intro h X n p lam hp hl w hw L hL
  refine le_antisymm ?_ ?_
  · rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, delLeNab X.K X.Tau n lam _ hx⟩
  · exact GlobalTheory.ColPeriod.WeylLoc.nabLeDel_of_local (GlobalTheory.Published.weylDualWeylLatticesAgree_of_lowest_alcove h) X.K X.Tau n lam _
      (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau n X.emb τ L hL)) p w hp hw
      fun τ => spread_lt_of_two_mul_lt hp (lam τ) (hl τ)

end GlobalTheory.KerT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
section
namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

theorem tameList_eq {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : DC.tameList χ = Formalism.MainNotions.tameList χ := by
  funext o
  rcases o with _ | ⟨j, _ | _⟩ <;> rfl

theorem tameDistinct_iff (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) :
    DC.TameDistinct r g χ ↔ Formalism.MainNotions.TameDistinct r g χ := by
  unfold DC.TameDistinct Formalism.MainNotions.TameDistinct
  rw [tameList_eq]

end GlobalTheory.EX.DQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValues
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.Host (HChar atFin IsUnitAt IsUnifAt)
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv Neutral.B1

namespace GlobalTheory.TwistVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem evP_toRInt (P : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E) :
    evP F P (toRInt F E b : AfE F E) = algebraMap E (P.adicCompletion E) (b : E) := by
  change afIso F E ((b : E) ⊗ₜ[F] 1) P = _
  rw [afIso_tmul_one]
  rfl

theorem valued_lt_of_mem {P : HeightOneSpectrum (𝓞 E)} {w : RInt F E} (h : w ∈ P.asIdeal.map (toRInt F E)) :
    Valued.v (evP F P (w : AfE F E)) < 1 := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [evP_toRInt, Formalism.UG.P.levelaf_valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hb
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 a.2 P)) hx

theorem val_le_two {P : HeightOneSpectrum (𝓞 E)} {z : RInt F E} (hz : z ∈ (P.asIdeal ^ 2).map (toRInt F E)) :
    Valued.v (evP F P (z : AfE F E)) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
  GlobalTheory.UnifConj.val_le_of_mem (afIso F E) (afIso_tmul_one F E) (mem_rInt_iff F E) P 2 z hz

theorem exp_neg_two_lt {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) :
    WithZero.exp (-((2 : ℕ) : ℤ)) < Valued.v (algebraMap E (P.adicCompletion E) (b : E)) := by
  rw [GlobalTheory.SuppIdele.val_algebraMap, ← not_le, P.intValuation_le_pow_iff_mem]
  exact hb2

theorem value_of_congr2 (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) {P : HeightOneSpectrum (𝓞 E)} {u : (AfE F E)ˣ}
    {y : RInt F E} (hy : (y : AfE F E) = u) {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) {x : Eˣ} (hx : (x : E) = b)
    (h1 : y - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → y - 1 ∈ Q.asIdeal.map (toRInt F E)) :
    σ ((μ u : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by
  have hb := exp_neg_two_lt hb2
  have a1 : Valued.v (evP F P (u : AfE F E) - algebraMap E (P.adicCompletion E) (b : E)) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    have := val_le_two h1
    rwa [AddSubgroupClass.coe_sub, map_sub, evP_toRInt, hy] at this
  have a2 : ∀ Q, Q ≠ P → Valued.v (evP F Q (u : AfE F E) - 1) < 1 := fun Q hQ => by
    have := valued_lt_of_mem (h2 Q hQ)
    rwa [AddSubgroupClass.coe_sub, map_sub, Subring.coe_one, map_one, hy] at this
  set l := finAf F E (localIdele E P (atFin P x)) with hl
  have key : ∀ Q, Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) - 1) < 1 := fun Q => by
    have e1 : evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) * evP F Q (l : AfE F E) = evP F Q (u : AfE F E) := by
      rw [← map_mul, ← Units.val_mul, div_mul_cancel]
    have e2 : evP F Q (l : AfE F E) = ev Q (localIdele E P (atFin P x) : AdeleRing (𝓞 E) E) :=
      GlobalTheory.Mem.ReadTwist.afIso_finAf_apply _ Q
    by_cases hQ : Q = P
    · subst hQ
      rw [ev_local_self] at e2
      have e3 : ((atFin Q x : (Q.adicCompletion E)ˣ) : Q.adicCompletion E) = algebraMap E _ (b : E) := by
        rw [← hx]; rfl
      rw [e2, e3] at e1
      rw [← e1, ← sub_one_mul, map_mul] at a1
      by_contra hn
      push_neg at hn
      exact absurd (lt_of_lt_of_le hb (le_mul_of_one_le_left' hn)) (not_lt.2 a1)
    · rw [ev_local_ne hQ] at e2
      rw [e2, mul_one] at e1
      rw [e1]
      exact a2 Q hQ
  have hu : u / l ∈ intU F E := by
    refine (mem_intU_iff (u / l)).2 fun Q => ?_
    change Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E)) = 1
    have := key Q
    rw [← map_one (Valued.v : Valuation (Q.adicCompletion E) _)] at this ⊢
    exact Valuation.map_eq_of_sub_lt _ (by simpa using this)
  have hk : u / l ∈ μ.ker := by
    refine ker_of_reads h (map_toIdl_eq_one ht hu fun Q _ => le_exp_neg_one ?_)
    rw [map_sub, map_one]
    exact key Q
  rw [MonoidHom.mem_ker, map_div, div_eq_one] at hk
  rw [hk]
  exact (h _).symm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  intro F E _ _ _ _ _ K _ σ μ ξ h ht P
  have hne : ∀ {b : 𝓞 E}, b ∉ P.asIdeal ^ 2 → (b : E) ≠ 0 := fun {b} hb e =>
    hb ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  constructor
  · intro hunr
    have hv : ∀ {c : 𝓞 E}, c ∈ P.asIdeal → (hc2 : c ∉ P.asIdeal ^ 2) →
        ((ξ.locK P (Units.mk0 _ (hne hc2)) : ℂˣ) : ℂ) = ((ξ.val P : ℂˣ) : ℂ) := fun {c} hc hc2 => by
      refine congrArg _ (ξ.val_eq hunr _ ?_)
      show Valued.v (algebraMap E (P.adicCompletion E) (c : E)) = _
      exact GlobalTheory.UnifConj.val_of_cong P _ c hc hc2 (by rw [sub_self, map_zero]; exact zero_le')
    obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
      have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
      simpa using this
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ) :=
      (value_of_congr2 h ht a1 hb2 (x := Units.mk0 _ (hne hb2)) rfl a3 a4).trans (hv hb hb2)
    have hex : ∃ k, IsUnifVal μ P k := by
      refine ⟨μ y, fun w _ z z₀ c f1 hc hc2 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy, ← hv hc hc2]
      exact value_of_congr2 h ht f1 hc2 rfl f3 f4
    unfold unifVal
    rw [dite_eq_left hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ b a1 hb hb2 a2 a3 a4)]
    exact hy
  · intro hq q hqe
    set b : 𝓞 E := ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) with hbdef
    have hqb : (q : E) = (b : E) := by rw [hqe, hbdef]; simp
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ) := value_of_congr2 h ht a1 hq hqb a3 a4
    have hex : ∃ k, IsQValC μ P k := by
      refine ⟨μ y, fun w _ z z₀ f1 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy]
      exact value_of_congr2 h ht f1 hq hqb f3 f4
    unfold qVal qValC
    rw [dite_eq_left hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ a1 a2 a3 a4)]
    exact hy

end GlobalTheory.TwistVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.EX.DQ NumberField IsDedekindDomain

namespace GlobalTheory.EX.DQ


set_option maxHeartbeats 2000000 in
theorem twGoodOne_setDiv (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b))
    (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (p : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (H : TwGoodOne D ⟨twEOf O.xd, N0, S⟩ i b Q k p) :
    TwGoodOne (setDiv D N h) ⟨twEOf (O.tr N h).xd, N0, S⟩ i b Q k p := by
  unfold TwGoodOne at H ⊢
  have e1 : AvRec (setDiv D N h) = AvRec D := rfl
  have e2 : twEps (setDiv D N h) i = twEps D i := rfl
  rw [e1, e2]
  unfold IntegralHeckeForms.GoodTw at H ⊢
  obtain ⟨h1, ⟨eB, h2, h3, h4⟩, h5, h6, h7, h8⟩ := H
  exact ⟨h1, ⟨eB, h2, h3, h4⟩, fun j hj c => ⟨(h5 j hj c).1, (h5 j hj c).2⟩, h6, h7, h8⟩

theorem qd_setDiv : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    QD D O → QD (setDiv D N h) (O.tr N h) := by
  rintro D O N h ⟨h1, ⟨hc, N0, S, hS⟩, h3⟩
  refine ⟨h1, ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, fun a ha => ?_⟩⟩, h3⟩
  exact twGoodOne_setDiv D O N h N0 S _ _ _ _ _ ((hS w hw).2 a ha)

end GlobalTheory.EX.DQ
end

