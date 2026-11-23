module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMulMemInvHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmapToAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdempotentSubOneMemPlaceIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

theorem smul_mem_wLf_of_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (hc : c ∈ wInt X w) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    c • y ∈ Formalism.L2.SG.RowDict.wLf X w := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, ha, rfl⟩ := hc
    exact GlobalTheory.Mem.SymFrame.inclE_smul_mem_wLf X w a ha hy
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul r a _ ha =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r ha

theorem mem_wInt_of_mem_idS (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E))
    {s : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E}
    (hs : s ∈ idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal) :
    (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  let J : Ideal (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :=
    { carrier := {s | (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w}
      add_mem' := fun {a b} ha hb => by
        show ((a + b : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [Subring.coe_add]; exact add_mem ha hb
      zero_mem' := by
        show ((0 : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        rw [ZeroMemClass.coe_zero]; exact zero_mem _
      smul_mem' := fun r {a} ha => by
        show ((r * a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
        exact (wInt X w).smul_mem r ha }
  have hle : idS X.B.I.F (Formalism.L2.SG.Pf.RowDictPf.wB X w).asIdeal ≤ J := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show ((oToS X.B.I.F X.B.I.E a : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) :
      X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w
    refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, rfl⟩, ?_⟩
    rw [oToS_coe]
    rfl
  exact hle hs

end GlobalTheory.Mem.SymChar

namespace GlobalTheory.Mem.SymChar

theorem sigA_ew_sub_one_mem_wInt : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X _ _ kv hg hne
  set w := D.naut.plGw kv.1 kv.2 with hw
  have h1 : 1 - X.ew - sigA X.B.I X.ew ∈ wInt X w :=
    wInt_of_zmod X kv.1 hg (Formalism.L2.SG.Pf.SatGram.one_sub_ew X)
  let PP := Formalism.L2.SG.Pf.RowDictPf.wB X w
  let e : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  have hidem : e * (1 - e) = 0 := by
    apply Subtype.ext
    show X.ew * (1 - X.ew) = 0
    rw [mul_sub, mul_one, X.ew_idem, sub_self]
  have hr : resS X.B.I.F PP e * resS X.B.I.F PP (1 - e) = 0 := by rw [← map_mul, hidem, map_zero]
  have he : X.ew ∈ wInt X w := by
    rcases mul_eq_zero.1 hr with h | h
    · exact mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP e).1 h)
    · exfalso
      apply hne
      intro y hy
      have := mem_wInt_of_mem_idS X w ((resS_eq_zero_iff PP (1 - e)).1 h)
      exact smul_mem_wLf_of_mem_wInt X w this hy
  have e2 : sigA X.B.I X.ew - 1 = -X.ew - (1 - X.ew - sigA X.B.I X.ew) := by ring
  rw [e2]
  exact sub_mem (neg_mem he) h1

end GlobalTheory.Mem.SymChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeEqTotDeg
section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar)

namespace JetEx

@[reducible] def hostFields {R : Ranks} (H : Host R) : Fields where
  F := H.F
  E := H.E
  K := H.E
  starE := H.cmStar
  starK := H.cmStar
  Tau := Tau R
  deTau := Classical.decEq _
  emb τ := (H.sigmaOf (τ : R.GG) : H.E →+* H.E)

def hostAmb {R : Ranks} {H : Host R} (J : AmbIn H) (χ : Submodule (𝓞 H.E) H.E → ℂ) : Amb (hostFields H) where
  σ₀ := H.φ₀
  δ := J.δ
  d := H.d
  sc := (TaylorLogMetric.area (Th.lamOf H ⊤ J.δ))⁻¹
  AA := Th.perAA H ⊤
  cD := J.cD
  e a b N N' := J.V.eNat χ a b N N'
  chiF a b N N' := Th.chiFac H χ a b N N'

theorem jetSet_amb (B : Base) (J : AmbIn B.host) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (a b : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 B.host.E))) (M n : ℕ) :
    jetSet (J.amb B χ) a b S M n = jetSet (hostAmb J χ) a b S M n := by
  have h : B.fields.embC (J.amb B χ).σ₀ = (hostFields B.host).embC (hostAmb J χ).σ₀ := funext fun τ => B.fields_embC τ
  have h2 : ∀ N N' c x, (J.amb B χ).thInd (a := a) (b := b) S N N' c x = (hostAmb J χ).thInd S N N' c x := by
    intro N N' c x
    unfold Amb.thInd
    rw [h]
    rfl
  unfold jetSet
  simp only [h2]
  rfl


open Classical in
@[reducible] def hostWts (P : Pre) : Wts (hostFields P.host) P.Word P.R where
  row := fun τ => RowPar.of (P.hc τ)
  hc := P.hcW
  tops := Finset.univ.filter fun τ : Tau P.R => (τ : P.R.GG) ∈ P.host.topPlaces

def totDeg (P : Pre) (u : P.Word) (i : ℕ) : ℕ := (∑ τ, ∑ r, ((hostWts P).nuW u (i + 1) τ).w r).toNat

theorem degree_eq_totDeg (B : Base) (u : B.Word) (i : ℕ) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : e.degree = totDeg B.toPre u i := by
  have h1 : e.degree = ∑ τ, monoDeg e τ := by
    simp only [monoDeg_eq_sum]
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun τ _ => Fintype.sum_prod_type _
  have h2 : ((∑ τ, monoDeg e τ : ℕ) : ℤ) = ∑ τ, ∑ r, ((hostWts B.toPre).nuW u (i + 1) τ).w r := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => he τ
  rw [h1, totDeg, ← h2, Int.toNat_natCast]

def ramSet {R : Ranks} (H : Host R) (ξ : HChar H.E) : Set (HeightOneSpectrum (𝓞 H.F)) :=
  {v | ¬ ∀ a : Ideles H.E, finAf H.F H.E a ∈ inertAt H.E v → ξ.1 a = 1}

theorem qprime_eq_ramSet {R : Ranks} (H : Host R) {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr H.F H.E K} {ξ : HChar H.E}
    (h : Reads σ μ ξ) : Qprime μ = ramSet H ξ := by
  have key : ∀ a, ξ.1 a = 1 ↔ μ (finAf H.F H.E a) = 1 := fun a => by
    rw [Units.ext_iff, h a, Units.ext_iff, Units.val_one, Units.val_one, map_eq_one_iff _ σ.injective]
  ext v
  refine not_congr ⟨fun h1 a ha => (key a).2 (h1 ha), fun h1 y hy => ?_⟩
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E y
  exact (key a).1 (h1 a hy)

def badP (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  (⋃ u, {Q | ((P.T u : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal}) ∪ (⋃ i, {Q | ((P.host.g i : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal}) ∪
    ⋃ ξ ∈ {ξ ∈ Ξ | (ramSet P.host ξ).Finite}, ⋃ v ∈ ramSet P.host ξ, {Q | Q.asIdeal.under (𝓞 P.host.F) = v.asIdeal}

theorem finite_mem {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    {Q : HeightOneSpectrum (𝓞 E) | a ∈ Q.asIdeal}.Finite := by
  simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)

theorem badPrimes_finite₂ (P : Pre) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) : (badP P Ξ).Finite := by
  have hfin : {ξ ∈ Ξ | (ramSet P.host ξ).Finite}.Finite := h.subset fun _ hξ => hξ.1
  refine ((Set.finite_iUnion fun u => finite_mem ?_).union (Set.finite_iUnion fun i => finite_mem ?_)).union
    (hfin.biUnion fun ξ hξ => Set.Finite.biUnion hξ.2 fun v _ => ?_)
  · exact Nat.cast_ne_zero.2 (P.T_prime u).ne_zero
  · exact Nat.cast_ne_zero.2 (P.host.g_prime i).ne_zero
  · obtain ⟨a, ha, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine (finite_mem (a := algebraMap (𝓞 P.host.F) (𝓞 P.host.E) a) ?_).subset fun Q hQ => ?_
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 h0
    · have : a ∈ Q.asIdeal.under (𝓞 P.host.F) := hQ ▸ ha
      exact this

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {Q : HeightOneSpectrum A} (h : Q ∈ divs a) :
    a ∈ Q.asIdeal := by
  unfold divs at h
  split_ifs at h with h1
  · exact h1.mem_toFinset.1 h
  · simp at h

variable {B : Base} {X : PreX B.toPre}

theorem rowSG_subset {I : ColIn B X} (h : I.Ok) (a : I.ι) :
    ∀ Q ∈ rowSG (B.primes X) I.sel (I.tup a), Q ∈ badP B.toPre (Set.range I.xi) := by
  classical
  intro Q hQ
  rcases Finset.mem_union.1 hQ with hQ | hQ
  · obtain ⟨i, hi⟩ : ∃ i, Q ∈ (B.primes X).vG i := by
      rcases Finset.mem_union.1 hQ with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩))
    have := Q.asIdeal.mul_mem_left ((B.primes X).piG i) (mem_of_mem_divs hi)
    rwa [B.primes_piG_norm X i] at this
  · unfold QE at hQ
    split_ifs at hQ with h1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
      have e := qprime_eq_ramSet B.host (h.xi_reads a)
      exact Or.inr (Set.mem_iUnion₂.2 ⟨I.xi a, ⟨⟨a, rfl⟩, e ▸ h1⟩,
        Set.mem_iUnion₂.2 ⟨v, e ▸ h1.mem_toFinset.1 hv, h.sel_ok v⟩⟩)
    · simp at hQ

theorem Sb_subset {I : ColIn B X} (h : I.Ok) (a : I.ι) (u : B.Word) :
    ∀ Q ∈ I.Sb a u, Q ∈ badP B.toPre (Set.range I.xi) := by
  classical
  intro Q hQ
  rcases Finset.mem_union.1 hQ with hQ | hQ
  · refine Or.inl (Or.inl (Set.mem_iUnion.2 ⟨u, ?_⟩))
    have := Q.asIdeal.mul_mem_right (B.fields.conjO ((B.primes X).piT u)) (mem_of_mem_divs hQ)
    rwa [B.primes_piT_norm X u] at this
  · exact rowSG_subset h a Q hQ

section Lat

open Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves

theorem eNat_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (V : Formalism.L2.Ker.Base D cc δ) (hc : StandardLatticesGL3.Crv D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') : V.eNat χ a b L L' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) L L' := by
  have s0 := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D a)
  have s0' := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D b)
  have h0 := WeilVac.thZero_mem V (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ V hc) a b
  have h1 := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a b _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
    (Or.inr ⟨_, _, hL, s0', rfl⟩) _ h0).2.1
  have h2 := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a b _ _ (Or.inr ⟨_, _, hL, s0', rfl⟩)
    (Or.inr ⟨_, _, hL, hL', rfl⟩) _ h1).2.1
  exact GlobalTheory.InertSign.ThSp_smul (Formalism.L2.Ker.Base.chiFac χ a b L L') h2

theorem laHyp_empty {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (V : Formalism.L2.Ker.Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (hX : X.Ok) (hs : s.Ok) (hc : StandardLatticesGL3.Crv D cc δ) (ha : Even a) (hb : Even b) :
    (ambOf s V χ cD).LaHyp a b ∅ := by
  have hL := LatticeFacts.latAll V hc.1 hc.2
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ V χ cD hs
  have hq := qIntAll_of_latAll D cc δ V hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨delta_ne_zero V, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s V χ cD, fun N N' h h' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s V χ cD).sc)
    (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s V χ cD).d (ambOf s V χ cD).sc) (TaylorLogMetric.al D V.tor)
    (lam (ambOf s V χ cD) N N') (lam (ambOf s V χ cD) N N') (TaylorLogMetric.La D V.tor (s.lat N) (s.lat N'))
    (TaylorLogMetric.La D V.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
    (fun x hx => by
      obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
      exact alV_eq s V x hm)
    (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
  exact ⟨h3 (V.eNat χ a b (s.lat N) (s.lat N')) (eNat_mem V hc χ (hsd _ _ h) (hsd _ _ h')).2, h1, h2⟩

end Lat

theorem finAlg_step (hL : StagesInhab.HasLetters B.toPre) {I : ColIn B X} (h : I.Ok) (a : I.ι) (u : B.Word) (i j M n : ℕ)
    (hM : 0 < M) : FinAlg (jetSet I.A (B.R.N i) (B.R.N j) (I.Sb a u) M n) := by
  obtain ⟨⟨B, C, W, V, S, N, G⟩, rfl, -⟩ := StagesInhab.exists_stages_over B hL 1
  have hs := seamOf_ok B C W V S N G
  obtain ⟨hδ, hc⟩ := (AmbIn.ok_iff B C W V S N G I.J).1 h.amb_ok
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B C W V S N G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hχ : TaylorLogMetric.IsChi (assemble B C W V S N G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hi := GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N B.R i
  have hj := GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N B.R j
  have hA : I.A = ambOf (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD :=
    AmbIn.amb_eq_ambOf B C W V S N G I.J I.chi
  have hne : I.A.AA ≠ ⊥ := by
    rw [hA]
    exact GlobalTheory.ThetaMove.SeamMoves.aa_ne_bot _ _ _ _ top_ne_bot
  have hLa : I.A.LaHyp (B.R.N i) (B.R.N j) (I.Sb a u) := by
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes _ (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    have h0 := laHyp_empty (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD hX hs ⟨hcc, hδ⟩ hi hj
    rw [hA]
    exact ⟨h0.1, h0.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P
      (bad P hP).2.1 (bad P hP).2.2.1 (by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _), h0.2.2.2.2⟩
  have hE := _root_.GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B C W V S N G) _ hcc hδ hχ
  have hJ := _root_.GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg _ _ (seamOf B C W V S N G) _ _ (I.J.toRec B C W V S N G) I.chi I.J.cD _ _ hX hs hcc hδ hχ hi hj
  rw [← hA] at hJ
  refine JetFin.finAlg_jetSet _ _ _ _ _ _ _ hX hM hJ.1 (IndEq.thIndEq_of_vacEq _ _ _ _ _ _ hX hLa hne hM ?_) ?_ (hJ.2 _ _)
    fun τ => ?_
  · rw [hA]
    exact VacEqPf.vacEq_ambOf _ _ _ _ _ _ _ _ _ _ hs hE hi hj
  · rw [hA]
    exact ChiFacLaw.chiLaw_ambOf _ _ _ _ _ _ _ _ _ _ hs hχ
  · obtain ⟨K, _, -, hK⟩ := h.amb_ok.dgen
    obtain ⟨s, hs, -⟩ := hK τ
    rw [I.A_cD, ← hs]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom K.val

def amb0 {R : Ranks} (H : Host R) : AmbIn H := (exists_ambIn_ok H).choose

theorem qPow_ne_zero {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) : qOf Q ^ n ≠ 0 :=
  pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 Q.ne_bot)


end JetEx

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnChartsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperators_on_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}), I.ReadsK l Z u a i hi chOf K → (∀ β, FunKilled (K β).lev (X.piT u)) → I.IdY l Z u a i hi eY → I.IdV l u a eV → DilationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY eV chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  first | exact @GlobalTheory.Mem.Col2.DiaChart.dilTied | exact GlobalTheory.Mem.Col2.DiaChart.dilTied | (intros; apply GlobalTheory.Mem.Col2.DiaChart.dilTied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupActionLiftFormsRightTranslation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem formRho_one_apply {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
    (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)
    (h : Λ.grp) (v : C.V) :
    Formalism.L2.Col.formRho C Λ ((1 : Formalism.L2.Col.UF Xf.E n), h) v = ((Λ.chr h : Xf.Kˣ) : Xf.K) • v := by
  show (((Λ.chr h : Xf.Kˣ) : Xf.K) • C.rho 1) v = _
  rw [map_one]
  rfl

set_option maxHeartbeats 8000000 in
theorem act_key (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U)
    (A k : GL (Fin X.B.R.nV) (EA X)) (P : PresL X I hX U Xg tr L cV i t)
    (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q)
    (h : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1))
    (hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
    (hpt : ∀ x : Bridge.Gf (Vc X.toD7 i), ptS X I U i t A k (x * κ) =
      ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
        h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
        ptS X I U i t A k x)
    (hch : X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ))
    (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (x : Bridge.Gf (Vc X.toD7 i)) :
    P.coef (((Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ) φ :
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) :
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (ptL X I U i t A k x)) =
      (((envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptL X I U i t A k (x * κ))) := by
  have h1 := φ.2 (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ⟨h, hh⟩) :
      Formalism.L2.Col.FormG (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv)
      (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)
  have h2 : (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ)) =
      ((((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K)) •
        (φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x) := by
    rw [hpt x, ← one_mul (1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), ← Prod.mk_mul_mk, mul_smul]
    exact h1.trans (formRho_one_apply _ _ _ _)
  refine Eq.trans (congrArg P.coef (Formalism.L2.Col.trRep_apply _ _ _ _ _ φ _)) ?_
  have h3 : P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
      (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V) (ptS X I U i t A k (x * κ))) =
      (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) •
        P.coef ((φ : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).D →
          (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V)
        (((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
          (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ))⁻¹) •
          ptS X I U i t A k x)) := by
    rw [h2]
    refine (P.coef.map_smulₛₗ _ _).trans ?_
    rw [hch]
  exact (inv_smul_smul ((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ) _).symm.trans (congrArg _ h3.symm)

theorem lemT : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ h : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.nV) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
        ∃ hh : h ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
          (∀ x : Bridge.Gf (Vc X.toD7 i), LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
            ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV),
              h * (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ))⁻¹) •
              LiftBrg.ActQ.ptS X I U i t A k x) ∧
          X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨h, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
            (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG i t A k hA κ
  obtain ⟨hh, hc⟩ := GlobalTheory.T.flagLift_translation_mem_typeLevel_character X px I U L eG hI hV hL hG i t A k hA κ
  refine ⟨_, hh, fun x => ?_, hc⟩
  rw [_root_.GlobalTheory.Mem.R3.LiftBrg.ActQ.ptS_mul_Q X px I U L hI hV hL i t A k hA κ x, mul_inv_cancel_right]

set_option maxHeartbeats 4000000 in
theorem lemAct : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∀ (g : Gc X.B px) (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q), LiftBrg.ActQ.redQ X I U L eG i t κ = g →
      ∀ f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms,
        P.ext ((((famR X I hX U Xg tr).A.leftGroupActionLift i t g f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms)) : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V) =
          Bridge.g0Act (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP g κ hκ f
  obtain ⟨h, hh, hpt, hch⟩ := lemT X px I U L eG hI hV hL hG i t A k hA κ
  subst hκ
  funext x
  have e1 := hP ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f) x
  have e2 := hP f (x * κ)
  unfold Bridge.g0Act
  refine e1.trans ?_
  refine Eq.trans ?_ (congrArg (fun w => (((LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch κ)⁻¹ : ℂˣ) • w) e2).symm
  have e3 : (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
      ((famR X I hX U Xg tr).A.leftGroupActionLift i t (redQ X I U L eG i t κ) f)) =
      Formalism.L2.Col.unipotentRightActionFormsV X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1) (redQ X I U L eG i t κ)
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f) :=
    LinearEquiv.symm_apply_apply _ _
  rw [e3]
  exact act_key X I hX U Xg tr L eG cV i t A k P κ h hh hpt hch _ x

theorem exists_actTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∃ a : Bridge.ActTie (Bridge.ratF (Vc X.toD7 i)) P (LiftBrg.envL X I hX U Xg tr L cV i t).lev.Q
        (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch ((famR X I hX U Xg tr).A.leftGroupActionLift i t),
      ∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG (a.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP
  refine ⟨{ red := redQ X I U L eG i t
            red_surj := GlobalTheory.T.levelGroup_reduction_onto_finite_group_surjective X px I U L eG hI hV hL hG i t
            red_ker := fun q => redQ_eq_one_iff X I U L eG i t q
            act_eq := lemAct X px I hX U Xg tr L eG hI hV hL hG cV i t A k hA P hP }, fun q => ?_⟩
  exact eG_redQ X I U L eG i t q

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_group_goodSet_levels_characters : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), IsPlacewiseIdentity X (px := px) eG ∧ GoodSet X (px := px) (eG.trans cG) Xg ∧ PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) ∧ (∀ g, (idemOf Xg).coeff g ∈ X.B.Ks) ∧ (∀ p, ((chr0 I p : X.B.LLˣ) : X.B.LL) ∈ X.B.Ks) ∧ ∀ tr, IdemClass (D := X.toD7) (famR X I hX U Xg tr).A ∧ Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 ∧ ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  first | exact @GlobalTheory.Mem.R3.Grp.grp_levels_exist | exact GlobalTheory.Mem.R3.Grp.grp_levels_exist | (intros; apply GlobalTheory.Mem.R3.Grp.grp_levels_exist <;> assumption)
end

