module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0002

@[expose] public section

noncomputable section
namespace GlobalTheory.TwInputs.JoinModel
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section General

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}

variable {G : Type} [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw}
  {YS : NExpRealS R cG S} {cf : CharFrame D}

theorem psi_of_grp (h : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) (Z : ExportTie YS geo.v₀) (i b) (g : F.P0)
    (hg : cG (R.eG g) ∈ D.nexp.U) :
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, hg⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (F.ψ0 g : D.what₂.LLˣ))⁻¹ := by
  obtain ⟨x, hx, e⟩ := h.psi0 g hg i b
  have h1 := Z.good.e_LL0 i b x
  refine (congrArg (Z.ρ.e i b) e).trans (h1.trans ?_)
  change D.what₂.embLL (x : D.what₂.LL) = _
  rw [hx, Units.val_inv_eq_inv_val, map_inv₀]

theorem low_of_tied {Fr : TwFrame D} (h : NTwTied D Fr) (hq : D.host.q ∣ (NumberField.discr D.host.E).natAbs) (i) (P : PlE D.host)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
      𝓞 D.host.E) ∈ P.asIdeal) : P ∈ D.ntw.S0 i := by
  have hp := P.isPrime
  have mem : ∀ p : ℕ, placesOver D.host.E p ⊆ ↑(D.ntw.S0 i) → ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i :=
    fun p a b => a b
  have key : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    intro m
    induction m using Nat.recOnMul with
    | zero => exact fun h0 => absurd rfl h0
    | one => exact fun _ h1 => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h1)) hp.ne_top
    | prime p pp => exact fun _ h1 => ⟨p, pp, dvd_rfl, h1⟩
    | mul a b iha ihb =>
      intro h0 h1
      rw [Nat.cast_mul] at h1
      rcases hp.mem_or_mem h1 with h1 | h1
      · obtain ⟨p, p1, p2, p3⟩ := iha (left_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_right _, p3⟩
      · obtain ⟨p, p1, p2, p3⟩ := ihb (right_ne_zero_of_mul h0) h1
        exact ⟨p, p1, p2.mul_left _, p3⟩
  simp only [Nat.cast_mul] at hP
  rcases hp.mem_or_mem hP with hP | hP
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · obtain ⟨p, p1, p2, p3⟩ := key _ D.host.QS_pos.ne' hP
        exact mem p ((h.two_ramified_places_subset_S0 i).2 p p1 ((D.host.dvd_natAbs_discr_iff p1).2 (p2.trans D.host.QS_dvd_condN))) p3
      · exact mem _ ((h.two_ramified_places_subset_S0 i).2 _ D.host.hyp.1 hq) hP
    · have hN : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      obtain ⟨p, p1, p2, p3⟩ := key _ hN hP
      exact mem p (h.norm_ccK_places_subset_S0 i p p1 p2) p3
  · rcases hp.mem_or_mem hP with hP | hP
    · rcases hp.mem_or_mem hP with hP | hP
      · rcases hp.mem_or_mem hP with hP | hP
        · exact mem _ (D.ntw.placesOver_subset_exceptional i 0) hP
        · exact mem _ (D.ntw.placesOver_subset_exceptional i 1) hP
      · exact mem _ (by rw [h.ringSpec_excludedPlaces_eq i]; exact fun Q hQ => Or.inl (Or.inl (Or.inr hQ))) hP
    · exact mem _ (by rw [h.ringSpec_excludedPlaces_eq i]; exact fun Q hQ => Or.inl (Or.inr hQ)) hP

theorem conj_of_lev {P P' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.IndefR.Lev.IsConjPl P P') : Formalism.BasicNotions.IsConjPl D.host P P' := by
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  let φ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)
  have hφ : ∀ x : 𝓞 D.host.E, ((φ x : 𝓞 D.host.E) : D.host.E) = D.host.conj x := fun _ => rfl
  have le : P.asIdeal ≤ P'.asIdeal.comap φ := fun c hc => by
    obtain ⟨c', h1, h2⟩ := h c hc
    have : φ c = c' := RingOfIntegers.ext (by rw [hφ, h2, hs])
    exact Ideal.mem_comap.2 (this ▸ h1)
  have e := P.isMaximal.eq_of_le (Ideal.comap_ne_top φ P'.isPrime.ne_top) le
  intro x y hxy
  have : y = φ x := RingOfIntegers.ext (by rw [hφ, hxy])
  rw [this, e]
  rfl

theorem baseTup_of {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw)
    (t : X.T) (ht : X.R.xiH t = X.R.C.delAt (D.ntw.l i)) : BaseTup Y i := fun j b => by
  have hL := X.char.lev
  refine ⟨t, (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 _ _ _ (ht ▸ hL.xi t) (Y.Z.pin.delta i j b), ?_⟩
  have hd : IsDelta (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) (X.R.xiH t) := by
    rw [ht, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have ram : ∀ P, ¬ (X.R.xiH t).UnrAt P ↔ P ∈ D.ntw.pD i := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq i]
    refine ⟨fun h => by_contra fun h' => h (hd.unr P h'), fun h hu => ?_⟩
    have := (hd.ine P h 1).1 fun x hx => by rw [pow_one]; exact hu x hx
    omega
  have fw : ∀ P ∈ X.R.Q t, P ∈ D.ntw.pD i ∧ P ∈ Y.Z.ρ.ch i := fun P hP =>
    have h1 := (ram P).1 ((hL.Q_ram t P).2 (Or.inl hP))
    ⟨h1, Y.Z.pin.deltaPl i t P hP h1⟩
  rw [Y.Z.good.delta i j b]
  ext P
  change _ ↔ P ∈ half _ _
  refine Iff.trans ?_ (by classical simp only [half, Finset.mem_filter] : P ∈ D.ntw.pD i ∧ P ∈ Y.Z.ρ.ch i ↔ P ∈ half (Y.Z.ρ.ch i) (D.ntw.pD i))
  refine ⟨fw P, fun ⟨h1, h2⟩ => ?_⟩
  rcases (hL.Q_ram t P).1 ((ram P).2 h1) with h | ⟨P', h, hc⟩
  · exact h
  · by_cases e : P' = P
    · exact e ▸ h
    · exact absurd h2 (((Y.Z.good.ch i).pair P' P (conj_of_lev hc) e).1 (fw P' h).2)

theorem q_dvd_discr (D : D7) : D.host.q ∣ (NumberField.discr D.host.E).natAbs :=
  Int.natCast_dvd.1 D.host.q_dvd_discr

end General

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

def realOf (t : RowsT K w Z Wt p0) (hH : HostHyp (w.st Z).toD7) (hV : ∀ j, FWT.VStd (w.st Z).toD7 j)
    (hs : 8 * B.R.f * B.R.r + 4 ≤ B.R.nV) : RealSide (w.st Z).toD7 where
  Γ := _
  Pl0 := _
  I0 := _
  T := _
  A3 := _
  core := t.r.z.core
  R := t.r.z.R
  F := t.r.z.F
  cG := t.r.z.cG
  geo := t.r.z.geo
  char := RealDat3.characterisation_of_weak t.r.z.pins.char t.exAt
  phs := t.r.z.pins.phs
  guard := t.r.z.pins.keep.guard
  valKs := t.r.z.pins.keep.valKs
  idem := t.r.z.good.2
  unif := t.r.intersectionNumber_baseChange.prim.unif
  integral := t.r.intersectionNumber_baseChange.aux.integral
  inGeo := t.inGeo
  finT := Finite.of_injective _ (R3.ixOf_injective w.I _)
  host := hH
  std := hV
  size := hs

variable {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch} {xd : ThData (w.D Z)} {c : NCore hL t n}

theorem base_of_untw {hH hV hs} (Y : SerSide (realOf t hH hV hs) (twEOf xd)) (hT : T = TwDat.untw B T.pl) (v : B.places.Pl)
    (hv : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0) : BaseTup Y (nch.twI v) := by
  refine baseTup_of Y _ (t.r.z.R.mu ((w.D Z).plEq v)) ?_
  have hW : v ∈ Wt := by_contra fun h => hv (t.mu.off v h)
  have h1 := (t.r.z.mu v).2
  rw [if_pos hW] at h1
  have hp : T.psi v = 1 := by rw [hT]; rfl
  refine ((t.r.z.lev.xiH _).trans h1).trans ?_
  refine Eq.trans ?_ (congrArg₂ CharFrame.delAt t.r.z.lev.C (nch.twI_l v)).symm
  unfold TwDat.xiTw
  rw [hp, mul_one]
  rfl

end Rows

end GlobalTheory.TwInputs.JoinModel

end
