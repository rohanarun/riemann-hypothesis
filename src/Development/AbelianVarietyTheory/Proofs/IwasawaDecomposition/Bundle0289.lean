module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalEigenvaluesIndependentOfStandardFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

theorem nonempty_equiv_zmod (k : Type) [Ring k] {p : ℕ} (hp : p.Prime) (h : Nat.card k = p) : Nonempty (ZMod p ≃+* k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  have := Fintype.ofFinite k
  exact ⟨ZMod.ringEquivOfPrime k hp (by rw [← Nat.card_eq_fintype_card, h])⟩

noncomputable def transport {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) : MulChar k ℂ where
  toMonoidHom := χ.toMonoidHom.comp (e : k →* k')
  map_nonunit' a ha := χ.map_nonunit fun h => ha (by simpa using h.map e.symm)

theorem transport_apply {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) (a : k) :
    transport e χ a = χ (e a) := rfl

theorem orderOf_ofUnitHom {p : ℕ} (hp : p.Prime) (om : (ZMod p)ˣ →* ℂˣ) (h : Function.Injective om) :
    orderOf (MulChar.ofUnitHom om) = p - 1 := by
  have := Fact.mk hp
  have key : ∀ n : ℕ, MulChar.ofUnitHom om ^ n = 1 ↔ p - 1 ∣ n := by
    intro n
    rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card, ← IsCyclic.exponent_eq_card,
      Monoid.exponent_dvd_iff_forall_pow_eq_one, MulChar.ext_iff]
    refine forall_congr' fun a => ?_
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
      ← map_pow, map_eq_one_iff om h]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((key _).2 dvd_rfl)) ((key _).1 (pow_orderOf_eq_one _))

section Orient

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField E] in
theorem exists_oriented (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (hx : x * σ x = (p : E)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) ∧ (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
      Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1 := by
  by_cases h : Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1
  · exact ⟨sp, h1, h2, h⟩
  refine ⟨sp.trans RingEquiv.prodComm, fun y => ?_, fun a => ?_, ?_⟩
  · rw [RingEquiv.trans_apply, h1]; rfl
  · rw [RingEquiv.trans_apply, h2]; rfl
  have e1 : (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 = (sp (inclE (F := F) (v.adicCompletion F) x)).1 :=
    congrArg Prod.snd (h1 (inclE (F := F) (v.adicCompletion F) x))
  have e2 : (sp (inclE (F := F) (v.adicCompletion F) x)).1 * (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 =
      (p : v.adicCompletion F) := by
    rw [← Prod.fst_mul, ← map_mul, ← map_mul, hx, map_natCast, map_natCast, Prod.fst_natCast]
  have e3 : Valued.v (p : v.adicCompletion F) < 1 := by
    have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [this, Examples₂.adicCompl_val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  show Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 < 1
  rw [e1]
  by_contra h'
  rw [← e2, map_mul] at e3
  exact absurd e3 (not_lt.2 (one_le_mul (not_lt.1 h') (not_lt.1 h)))

end Orient

section Generic

variable {X : Fields} {Pr : Primes X} {m : ℕ}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← hPr.vG_norm i w hw]
  exact Ideal.absNorm_mem _

theorem mem_vG_of_g_mem (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs)
    (h : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal) : w ∈ Pr.vG i := by
  classical
  have h1 : ∃ j, w ∈ Pr.vG j := by
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h0 | h0 <;> exact ⟨_, h0⟩
  obtain ⟨j, hj⟩ := h1
  by_cases e : j = i
  · exact e ▸ hj
  exfalso
  have hne : Pr.g j ≠ Pr.g i := by
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hc : IsCoprime ((Pr.g j : ℕ) : 𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr hj)) (Ideal.mul_mem_left _ _ h)

theorem mem_vGs {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union.2 (Or.inl hw)
  · exact Finset.mem_union.2 (Or.inr hw)

theorem exists_gLoc (Ch : Chars X Pr m) (hf : 0 < X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (cm : CMData X.F X.E) (σ₀ : X.K →+* ℂ)
    (hs : ∀ i, GlobalTheory.St.G.SplitsIn X.E (Pr.g i)) :
    ∃ G : GLoc X.F X.E cm.sig Pr.g, G.piG = Pr.piG ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ n : ℕ,
        G.psi0 j v h (n : kv X.F v) = σ₀ (Ch.psi0 w (n : 𝓞 X.E ⧸ w.1.asIdeal))) ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ (s : Fin m) (n : ℕ)
        (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 X.E ⧸ w.1.asIdeal) = n →
        G.chiB j v h s.1 (n : kv X.F v) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K)) ∧ CharacterCompatible G m := by
  classical
  have hnorm : ∀ i, (Pr.piG i : X.E) * cm.sig (Pr.piG i : X.E) = (Pr.g i : X.E) := fun i => by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    simp only [map_mul, map_natCast] at this
    exact this
  have hsp := fun i => (GlobalTheory.St.G.SplitPrime.split_place X.F X.E cm (Pr.g i) (hPr.g_prime i) (hs i)).2
  have hor := fun i v h => exists_oriented cm.sig v (Pr.piG i : X.E) (Pr.g i) h (hnorm i) _ (hsp i v h).2.2.choose_spec.1
    (hsp i v h).2.2.choose_spec.2
  choose sp sp1 sp2 sp3 using hor
  have ev := fun i v h => (nonempty_equiv_zmod (kv X.F v) (hPr.g_prime i) (hsp i v h).1).some
  have hw0 : ∀ i, ∃ w, w ∈ Pr.vG i := fun i => Finset.card_pos.1 (by rw [hPr.vG_card i]; exact hf)
  choose w0 hw0 using hw0
  have ew := fun i w (hw : w ∈ Pr.vG i) => (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime i) (by
    rw [← hPr.vG_norm i w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  choose om omi hom using hCh.chi_om
  let om' : ∀ i, MulChar (ZMod (Pr.g i)) ℂ := fun i => MulChar.ofUnitHom ((Units.map (σ₀ : X.K →* ℂ)).comp (om i))
  have hin : ∀ {j v} (h : ((Pr.g j : ℕ) : 𝓞 X.F) ∈ v.asIdeal) (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → w.1 ∈ Pr.vG j := by
    rintro j v h w rfl
    refine mem_vG_of_g_mem hPr w.2 ?_
    have h' : algebraMap (𝓞 X.F) (𝓞 X.E) (Pr.g j : ℕ) ∈ w.1.asIdeal := h
    rwa [map_natCast] at h'

  have hval : ∀ j (w : {w // w ∈ Pr.vGs}) (hw : w.1 ∈ Pr.vG j) (s : Fin m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
      (om' j ^ (2 * (s.1 + 1))) ((ew j w.1 hw).symm c) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K) := by
    intro j w hw s c
    have := Fact.mk (hPr.g_prime j)
    let a : (ZMod (Pr.g j))ˣ := Units.map ((ew j w.1 hw).symm : _ →* _) c
    have ha : (ew j w.1 hw).symm c = (a : ZMod (Pr.g j)) := rfl
    have hc : (c : 𝓞 X.E ⧸ w.1.asIdeal) = (((a : ZMod (Pr.g j)).val : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) := by
      rw [← map_natCast (ew j w.1 hw), ZMod.natCast_zmod_val, ← ha, RingEquiv.apply_symm_apply]
    rw [hom j w hw s a c hc, ha, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl
  refine ⟨{ sp := sp, sp_sig := sp1, sp_alg := sp2, piG := Pr.piG, piG_norm := hnorm, sp_pi := sp3
            psi0 := fun i v h => ((σ₀ : X.K →* ℂ).compAddChar (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩)).compAddMonoidHom
              (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).toRingHom.toAddMonoidHom)
            psi_zero_nontrivial_character := ?_
            chiB := fun i v h a => transport (ev i v h).symm (om' i ^ (2 * (a + 1))) }, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v h h1
    apply hCh.psi_zero_nontrivial_character ⟨w0 i, mem_vGs (hw0 i)⟩
    ext x
    have h2 := DFunLike.congr_fun h1 (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x)
    have h3 : σ₀ (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩ (((ev i v h).symm.trans (ew i (w0 i) (hw0 i)))
      (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x))) = 1 := h2
    rw [RingEquiv.apply_symm_apply, map_eq_one_iff σ₀ σ₀.injective] at h3
    exact h3
  · intro j v h w hw n
    show σ₀ (Ch.psi0 ⟨w0 j, mem_vGs (hw0 j)⟩ (((ev j v h).symm.trans (ew j (w0 j) (hw0 j))) (n : kv X.F v))) = _
    rw [map_natCast]
    have := hCh.characterAgreesOnPlaces j ⟨w0 j, mem_vGs (hw0 j)⟩ w (hw0 j) (hin h w hw) (n : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at this
    rw [this]
  · intro j v h w hw s n c hc
    show transport (ev j v h).symm (om' j ^ (2 * (s.1 + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_natCast, ← hval j w (hin h w hw) s c, hc,
      map_natCast (ew j w.1 (hin h w hw)).symm]
  · intro i v h a b ha hb hab
    have h1 : om' i ^ (2 * (a + 1)) = om' i ^ (2 * (b + 1)) := by
      refine MulChar.ext' fun x => ?_
      have h2 : transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (ev i v h x) =
        transport (ev i v h).symm (om' i ^ (2 * (b + 1))) (ev i v h x) := DFunLike.congr_fun hab _
      rwa [transport_apply, transport_apply, RingEquiv.symm_apply_apply] at h2
    have h3 : (⟨a, ha⟩ : Fin m) = ⟨b, hb⟩ := by
      apply hCh.chi_inj ⟨w0 i, mem_vGs (hw0 i)⟩
      refine MonoidHom.ext fun c => Units.ext (σ₀.injective ?_)
      rw [← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨a, ha⟩ c, ← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨b, hb⟩ c, h1]
    exact congrArg Fin.val h3
  · intro i v h v' h' a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) =
      transport (ev i v' h').symm (om' i ^ (2 * (a + 1))) (n : kv X.F v')
    rw [transport_apply, transport_apply, map_intCast (ev i v h).symm, map_intCast (ev i v' h').symm]
  · intro i
    refine ⟨om' i, orderOf_ofUnitHom (hPr.g_prime i) _ ((Units.map_injective σ₀.injective).comp (omi i)), ?_⟩
    intro v h a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_intCast]

end Generic

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_gLoc_idG_chiTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g),
      I.IdG l Z G ∧ CharacterCompatible G B.R.m := by
  intro B X I hI _ l Z
  have hf : 0 < B.fields.f := by
    unfold Fields.f
    rw [Fintype.card_pos_iff]
    by_contra h
    have h1 := B.fields_f
    unfold Fields.f at h1
    rw [not_nonempty_iff] at h
    rw [Fintype.card_eq_zero] at h1
    unfold Ranks.f Ranks.n at h1
    have := B.R.ord_pos
    omega
  obtain ⟨G, h1, h2, h3, h4⟩ := exists_gLoc I.Ch hf l.pr hI.ch_ok B.sp.cm B.embLL (I.rec7 l Z).nd.g_split
  exact ⟨G, ⟨h1, h2, h3⟩, h4⟩

end GlobalTheory.Mem.TypePrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemOfFiniteTypeWithParts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

open GlobalTheory.Hk3 (Core Good IsSF SchurAll EEc Wcc IsLab SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.Mem.R3.LabEig

def IsSphScalars {D : D7} {V : HSp D} {n : ℕ} (Q : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  ∀ P d, IsLab V P d → ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ GlobalTheory.Hk3.hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) →
    principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V P d) x = c P d • x

theorem exists_isSphScalars {D : D7} {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E)
    (Q : principalLevelFrame.RowPsi V n) (hQ : StdPsi hF Q) (π : Formalism.L2.NG.FinTyp D.host.E n) : ∃ c, IsSphScalars Q π c := by
  have h : ∀ P d, ∃ a : ℂ, IsLab V P d → ∀ x ∈ π.S, (∀ κ, Q.ψ κ ∈ GlobalTheory.Hk3.hyp V P → Formalism.L2.NG.rt D.host.E n κ x = x) →
      principalLevelFrame.Hecke₃ Q (GlobalTheory.Hk3.rep V P d) x = a • x := by
    intro P d
    by_cases hd : IsLab V P d
    · obtain ⟨a, ha⟩ := GlobalTheory.SphScalar.spherical_scalar hF Q hQ π P d _ (GlobalTheory.Hk3.OpsRows.sphOp_rep hd)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using h
  exact ⟨c, hc⟩

theorem isotE_sub : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, IsSphScalars (PW i0) π c → ∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 π, ∃ x ∈ EEc R SF c, R.HE.e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF n hF PY PW hPY hPW π i0 c hEig b U hU
  obtain ⟨h, hOps, hNorm, -, -, hIn⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  obtain ⟨-, hg, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  obtain ⟨nY, hβY⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hi := hC.models.HE.1
  have hUi := Submodule.mem_inf.1 hU
  have hUE : U ∈ R.EEat (R.levR F b) := hUi.1
  have hUT : U ∈ R.EEat R.triv := GlobalTheory.GoodRowsLevel.eeat_le_triv R _ hUE
  obtain ⟨x, rfl⟩ : U ∈ LinearMap.range R.HE.e := by rw [hC.models.HE.2.1]; exact hUT
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Yc D 0) P d → h P (Finsupp.single d 1) x = star (c P d) • x := by
    intro P hP d hd
    have levY := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβY P
      (by rw [Nat.cast_pow]; exact fun hm => (hg _ P hP).1 (P.isPrime.mem_of_pow_mem nY hm))
      (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
    have hB := GlobalTheory.Hk3.OpsRows.sphOp_rep hd
    have hdW : IsLab (Wc D i0) P d := ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hP).2).2 hd
    have hB' := GlobalTheory.Hk3.OpsRows.sphOp_rep hdW
    have ha := hEig P d hdW
    obtain ⟨htr1, htr2⟩ := GlobalTheory.FrameTransport.sph_eigen_frame_indep hF PY (PW i0) hPY (hPW i0) P d
    have hvec : ∀ y ∈ (principalLevelFrame.FinTyp.conjT π).S, (∀ κ, PY.ψ κ ∈ GlobalTheory.Hk3.hyp (Yc D 0) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
        principalLevelFrame.Hecke₃ PY (GlobalTheory.Hk3.rep (Yc D 0) P d) y = star (c P d) • y := by
      intro y hy hfy
      have hy' : (fun g => star (y g)) ∈ π.S := hy
      have hfy' : ∀ κ, PY.ψ κ ∈ GlobalTheory.Hk3.hyp (Yc D 0) P →
          Formalism.L2.NG.rt D.host.E n κ (fun g => star (y g)) = fun g => star (y g) := by
        intro κ hκ
        rw [← principalLevelFrame.conj_rt, hfy κ hκ]
      have e := htr2 _ _ hB hB' _ hfy'
      rw [ha _ hy' (fun κ hκ => hfy' κ ((htr1 κ).2 hκ)), GlobalTheory.TypePart.heckeOperator_conj] at e
      funext g
      have e2 := congrArg star (congrFun e g)
      simp only [Pi.smul_apply, smul_eq_mul, star_star, star_mul'] at e2
      rw [Pi.smul_apply, smul_eq_mul, e2, mul_comm]
    have hfixU : ∀ k ∈ GlobalTheory.Hk3.hyp (Yc D 0) P, postOn (R.MY 0) (principalLevelFrame.rtA k) (R.HE.e x) = R.HE.e x := by
      intro k hk
      ext1 v
      rw [postOn_apply]
      funext g
      have := GlobalTheory.Hk3.OpsRows.mult_lev (goodPart_le _ _ _ _ _ hUT) v k (levY.1 k hk).1 g
      rw [(levY.1 k hk).2, one_mul] at this
      exact this
    have hU2 := GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF PY hPY R.θ (R.MY 0) (principalLevelFrame.FinTyp.conjT π) P d _ _ hB hvec _ hUi.2 hfixU
    apply hi
    rw [hOps P hP, map_smul, GlobalTheory.Hk3.OpsRows.hk_single]
    exact hU2
  refine ⟨x, hIn c x fun P d hP hd => ?_, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    simp
  have hdd : IsLab (Yc D 0) P (dualLab d) := by
    have l1 := GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hP
    exact l1.1.1 (l1.2.2 hd)
  have h1 := key P hP d hd
  have e := GlobalTheory.TypePart.star_eq_of_adj hNorm hP d hx0 h1 (key P hP _ hdd)
  have e' : star (c P d) = c P (dualLab d) := by
    rw [star_star] at e
    rw [e, star_star]
  rw [h1, e']

theorem isotL_sub : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), (∀ i, StdPsi hF (PW i)) → ∀ π i0 c, IsSphScalars (PW i0) π c → ∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (PW i) (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) (R.eWf i (sg0 D A)) π, ∃ x ∈ Wcc R SF i c, (R.HW i _).e x = U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF n hF PW hPW π i0 c hEig i U hU
  have hLev := hC.lev
  have hN : ∀ (cc : ℕ) (P : Pl D.host.E), (((1 ^ cc : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro cc P h
    rw [one_pow, Nat.cast_one] at h
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have LO := fun (j : Fin D.R.m) (Lv : LevelP R.Pg D.R.r ℂ) (P : Pl D.host.E) (hG : Good R A.μ0 P) =>
    GlobalTheory.LevOp.level_operators (Wc D j) (R.βW j) (R.ΛW j) _ (R.datWp j Lv) (hLev.βW j).choose_spec P
      (hN _ P) (fun PP h => hG PP (h.imp id (fun h' => absurd h' (Finset.notMem_empty _))))
  have hGood := fun P => (GlobalTheory.GoodPrimes.good_primes R F hLev).2.2.1 SF hSF P
  have hU' := hU
  simp only [principalLevelFrame.isotL, Mult.goodPart, Submodule.mem_inf, LinearMap.mem_ker] at hU'
  obtain ⟨⟨hUM, hUe⟩, hUiso⟩ := hU'
  have hle : ∀ k ∈ levS (Wc D i) (R.βW i) (R.datWp i R.triv),
      k ∈ levS (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) ∧
        levChi (Wc D i) (R.βW i) (R.datWp i (R.levL F false (sg0 D A))) k =
          levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k := by
    intro k hk
    obtain ⟨h1, h2⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) (R.levL F false (sg0 D A)) k hk
    obtain ⟨_, h3⟩ := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
    exact ⟨h1, h2.trans h3.symm⟩
  have hU0 : U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) :=
    GlobalTheory.HeckeParts.mult_mono hle hUM
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  obtain ⟨x, hx⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hrange]; exact hU0
  refine ⟨x, ?_, hx⟩
  rw [GlobalTheory.Hk3.Wcc, Submodule.mem_comap, hx]
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hU0, LinearMap.mem_ker.2 hUe⟩, Submodule.mem_inf.2 ⟨hU0, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  obtain ⟨_, _, _, _, hoff, -⟩ := id hB
  have hG : Good R A.μ0 P := (hGood P).1 hoff
  have hSph : SphOp (Wc D i) P d B := (((LO i R.triv P hG).2.1 SF d B).1 hB).2
  have hd0 : IsLab (Wc D i0) P d :=
    (GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i0 P d hG).2.2
      ((GlobalTheory.LabEq.isLab_W_iff (s := 1) R F hC i P d hG).2.1 ⟨B, hSph⟩)
  have hB0 := GlobalTheory.Hk3.OpsRows.sphOp_rep hd0
  have ha := hEig P d hd0
  obtain ⟨hiff, htr⟩ := GlobalTheory.FrameTransport.sph_eigen_frame_indep hF (PW i) (PW i0) (hPW i) (hPW i0) P d
  have hvec : ∀ y ∈ π.S, (∀ κ, (PW i).ψ κ ∈ GlobalTheory.Hk3.hyp (Wc D i) P → Formalism.L2.NG.rt D.host.E n κ y = y) →
      principalLevelFrame.Hecke₃ (PW i) B y = c P d • y := by
    intro y hy hfy
    rw [htr B _ hSph hB0 y hfy, ha y hy (fun κ hκ => hfy κ ((hiff κ).2 hκ))]
  have hUfix : ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, postOn (R.MW i (sg0 D A)) (principalLevelFrame.rtA k) U = U := by
    intro k hk
    obtain ⟨h1, h2⟩ := (LO i (R.levL F false (sg0 D A)) P hG).1 k hk
    have hl := principalLevelFrame.mult_lev hUM
    apply MultilinearMap.ext
    intro v
    funext g
    rw [Mult.postOn_apply]
    show U v (g * k) = U v g
    rw [hl v k h1 g, h2, one_mul]
  exact GlobalTheory.IsotSph.hecke_eq_smul_of_isot hF (PW i) (hPW i) R.θ (R.MW i (sg0 D A)) π P d B (c P d) hSph hvec U hUiso hUfix

theorem eig_parts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ c, (∀ b, ∀ U ∈ principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.EEc c, R.HE.e x = U) ∧ (∀ i, ∀ U ∈ principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A)) (principalLevelFrame.rowRepR R.θ (Y.eFT σ)), ∃ x ∈ R.Wc' i c, (R.HW i (sg0 D A3.A)).e x = U) := by
  intro hW hDS hHC hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨hC3, hSF, -, -, hEE, hWc, -⟩ := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hPins.char
  have hCore := hC3 hHolds.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  have hPY : StdPsi Y.hF Y.PY := Y.stdPsi.1
  have hPW : ∀ i, StdPsi Y.hF (Y.PW i) := Y.stdPsi.2
  obtain ⟨c, hc⟩ := exists_isSphScalars Y.hF (Y.PW ⟨0, Y.hm⟩) (hPW _) (principalLevelFrame.rowRepR R.θ (Y.eFT σ))
  refine ⟨c, fun b U hU => ?_, fun i U hU => ?_⟩
  · obtain ⟨x, hx, hxU⟩ := isotE_sub R.toRealDat F.lv2 hCore hS R.SF hSF Y.hF Y.PY Y.PW hPY hPW _ ⟨0, Y.hm⟩ c hc b U hU
    exact ⟨x, by rw [hEE]; exact hx, hxU⟩
  · obtain ⟨x, hx, hxU⟩ := isotL_sub R.toRealDat F.lv2 hCore R.SF hSF Y.hF Y.PW hPW _ ⟨0, Y.hm⟩ c hc i U hU
    exact ⟨x, by rw [hWc]; exact hx, hxU⟩

end GlobalTheory.Mem.R3.LabEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMCastSuccLast
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TilX

section Ext

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

def extM (_hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A) : Matrix (Fin N) (Fin N) A := fun a b =>
  if ha : a.1 < n then (if hb : b.1 < n then g ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else if b.1 < n then 0 else 1

theorem extM_castSucc (g : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc j.castSucc = g i j := by
  simp [extM]

theorem extM_castSucc_last (g : Matrix (Fin n) (Fin n) A) (i : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc (Fin.last n) = 0 := by
  simp [extM]

theorem extM_last_castSucc (g : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) j.castSucc = 0 := by
  simp [extM]

theorem extM_last_last (g : Matrix (Fin n) (Fin n) A) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) (Fin.last n) = 1 := by
  simp [extM]

theorem extM_mulVec_iC (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) (i : Fin n) :
    (extM hN g *ᵥ x) (Br.iC hN i) = (g *ᵥ iniH hN x) i := by
  subst hN
  have e : Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_castSucc, extM_castSucc_last, zero_mul, add_zero]
  rfl

theorem extM_mulVec_iL (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) :
    (extM hN g *ᵥ x) (Br.iL hN) = x (Br.iL hN) := by
  subst hN
  have e : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_last_castSucc, extM_last_last, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]

theorem extM_one : extM hN (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last]
  · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · rw [extM_castSucc, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castSucc_inj]

theorem extM_mul (g h : Matrix (Fin n) (Fin n) A) : extM hN (g * h) = extM hN g * extM hN h := by
  subst hN
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_castSucc_last]
  · simp [extM_castSucc, extM_castSucc_last, Matrix.mul_apply]

def extGL : GL (Fin n) A →* GL (Fin N) A :=
  Units.map { toFun := extM hN, map_one' := extM_one hN, map_mul' := extM_mul hN }

theorem extGL_val (g : GL (Fin n) A) : (extGL hN g : Matrix (Fin N) (Fin N) A) = extM hN g := rfl

theorem extGL_inv_val (g : GL (Fin n) A) :
    ((extGL hN g)⁻¹ : GL (Fin N) A).1 = extM hN ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  rw [← map_inv, extGL_val]

theorem eq_extM {M : Matrix (Fin N) (Fin N) A} {g : Matrix (Fin n) (Fin n) A}
    (h1 : ∀ (a : Fin N) (j : Fin n), M a (Br.iC hN j) = extM hN g a (Br.iC hN j))
    (h2 : ∀ a : Fin N, M a (Br.iL hN) = extM hN g a (Br.iL hN)) : M = extM hN g := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun j => ?_) b
  · exact h2 a
  · exact h1 a j

end Ext

end GlobalTheory.Mem.Col2.TilX

end
end

