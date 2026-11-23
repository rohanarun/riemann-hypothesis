module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompletionEquiv
section
open NumberField IsDedekindDomain IsLocalRing Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.GO.PlWitt
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaceOrbit

theorem exists_hom_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete J B] (f : R →+* A) (g : R →+* B) (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k → g x ∈ J ^ k) :
    ∃ h : A →+* B, ∀ (k : ℕ) a x, a - f x ∈ I ^ k → h a - g x ∈ J ^ k := by
  have hsur : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (I ^ k)).comp f) := fun k y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hs k a
    exact ⟨x, (Ideal.Quotient.eq.2 hx).symm⟩
  let u : (k : ℕ) → A ⧸ I ^ k →+* B ⧸ J ^ k := fun k =>
    RingHom.liftOfSurjective _ (hsur k) ⟨(Ideal.Quotient.mk (J ^ k)).comp g, fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hk k x (Ideal.Quotient.eq_zero_iff_mem.1 hx))⟩
  let φ : (k : ℕ) → A →+* B ⧸ J ^ k := fun k => (u k).comp (Ideal.Quotient.mk _)
  have hφ : ∀ k a x, a - f x ∈ I ^ k → φ k a = Ideal.Quotient.mk _ (g x) := fun k a x h => by
    change u k (Ideal.Quotient.mk _ a) = _
    rw [Ideal.Quotient.eq.2 h]
    exact RingHom.liftOfRightInverse_comp_apply ((Ideal.Quotient.mk (I ^ k)).comp f) _ _ _ x
  have hc : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (φ n) = φ m := by
    intro m n h
    refine RingHom.ext fun a => ?_
    obtain ⟨x, hx⟩ := hs n a
    rw [RingHom.comp_apply, hφ n a x hx, hφ m a x (Ideal.pow_le_pow_right h hx)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J φ hc, fun k a x h => ?_⟩
  rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hφ k a x h]

theorem eq_of_forall_pow {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {a b : A}
    (h : ∀ k : ℕ, a - b ∈ I ^ k) : a = b :=
  sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h k)

theorem exists_equiv_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B] (f : R →+* A) (g : R →+* B)
    (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k) (hs' : ∀ (k : ℕ) (b : B), ∃ x, b - g x ∈ J ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k ↔ g x ∈ J ^ k) : ∃ e : A ≃+* B, ∀ x, e (f x) = g x := by
  obtain ⟨h, hh⟩ := exists_hom_of_dense I J f g hs fun k x => (hk k x).1
  obtain ⟨h', hh'⟩ := exists_hom_of_dense J I g f hs' fun k x => (hk k x).2
  refine ⟨RingEquiv.ofRingHom h h' (RingHom.ext fun b => eq_of_forall_pow J fun k => ?_)
    (RingHom.ext fun a => eq_of_forall_pow I fun k => ?_), fun x => eq_of_forall_pow J fun k => ?_⟩
  · obtain ⟨x, hx⟩ := hs' k b
    simpa using sub_mem (hh k _ x (hh' k b x hx)) hx
  · obtain ⟨x, hx⟩ := hs k a
    simpa using sub_mem (hh' k _ x (hh k a x hx)) hx
  · exact hh k _ x (by simp)

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [hp : Fact p.Prime]

theorem exists_completion_equiv {v : HeightOneSpectrum (𝓞 F)} {i : F →+* Qn p n} (h : Good v i) :
    ∃ e : Qn p n ≃+* v.adicCompletion F, (∀ x : F, e (i x) = algebraMap F _ x) ∧
      ∀ y, y ∈ Set.range (algebraMap (Wn p n) (Qn p n)) ↔ e y ∈ v.adicCompletionIntegers F := by
  have hint := h.intAt
  have hd := h.dense
  obtain ⟨g, hg, -, hk⟩ := h
  have hinj := IsFractionRing.injective (Wn p n) (Qn p n)
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by rw [hk, map_natCast, cc_eq_zero]
  have hval : ∀ x : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) x : v.adicCompletionIntegers F) :
      v.adicCompletion F) = v.valuation F (x : F) := fun x => by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hpF : ∀ k : ℕ, ((p : F) ^ k) ≠ 0 := fun k => pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hvp : ∀ k : ℕ, Valued.v ((((p : v.adicCompletionIntegers F) ^ k : v.adicCompletionIntegers F)) :
      v.adicCompletion F) = v.valuation F ((p : F) ^ k) := fun k => by
    simpa using hval ((p : 𝓞 F) ^ k)
  have hvp0 : ∀ k : ℕ, v.valuation F ((p : F) ^ k) ≠ 0 := fun k => by simpa using hpF k
  haveI : IsAdicComplete (Ideal.span {(p : v.adicCompletionIntegers F)}) (v.adicCompletionIntegers F) :=
    (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ (by
      have := hval p
      rw [map_natCast] at this
      rw [this]
      exact (v.valuation_lt_one_iff_mem (K := F) _).2 hpv)
  obtain ⟨e, he⟩ := exists_equiv_of_dense (Ideal.span {(p : Wn p n)}) (Ideal.span {(p : v.adicCompletionIntegers F)})
    g (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    (fun k a => by
      obtain ⟨x, z, hx⟩ := hd a k
      rw [hg] at hx
      exact ⟨x, by rw [hinj hx, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact ⟨-z, by ring⟩⟩)
    (fun k b => by
      obtain ⟨x, hx⟩ := Idele.exists_valued_sub_le v (a := (b : v.adicCompletion F)) b.2
        (-WithZero.log (v.valuation F ((p : F) ^ k))).toNat
      refine ⟨x, ?_⟩
      rw [Ideal.span_singleton_pow, GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp]
      refine le_trans hx ?_
      conv_rhs => rw [← WithZero.exp_log (hvp0 k)]
      rw [WithZero.exp_le_exp]
      omega)
    (fun k x => by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
        GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp, hval,
        ← div_le_one₀ (zero_lt_iff.2 (hvp0 k)), ← map_div₀, ← GlobalTheory.UnramCompletion.intAt_iff, hint,
        Ideal.mem_span_singleton']
      refine exists_congr fun y => ?_
      rw [map_div₀, eq_div_iff ((_root_.map_ne_zero i).2 (hpF k)), hg, ← hinj.eq_iff]
      simp)
  refine ⟨IsFractionRing.ringEquivOfRingEquiv e, fun x => ?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · have : ((IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).toRingHom.comp i) =
        algebraMap F (v.adicCompletion F) :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun x => by
        change IsFractionRing.ringEquivOfRingEquiv e (i (x : F)) = _
        rw [hg, IsFractionRing.ringEquivOfRingEquiv_algebraMap, he]
        rfl)
    exact RingHom.congr_fun this x
  · rintro ⟨w, rfl⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact (e w).2
  · refine ⟨e.symm ⟨_, hy⟩, (IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).injective ?_⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, e.apply_symm_apply]
    rfl

theorem exists_first_frame {E : Type} [Field E] [NumberField E] [Algebra F E] {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) :
    ∃ fr : GL (Fin k) (w.adicCompletion F), ∀ t : Fin k → w.adicCompletion F,
      (∃ x ∈ Formalism.L2.Herm.locL w Λ, ∀ a, (φ (x a)).1 = t a) ↔
        ∀ a, ((fr⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  obtain ⟨B, -, -, hB, -⟩ := GlobalTheory.DualFrame.exists_dual_frames F E (AlgHom.id F E) k 1 (by simp) Λ hfin hsp w
  let π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom
  have hinv : (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      ((B⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _).map π := by
    rw [← map_inv]; rfl
  refine ⟨bc π B, fun t => ⟨?_, fun hu => ?_⟩⟩
  · rintro ⟨x, hx, hxt⟩ a
    have ht : t = π ∘ x := funext fun a => (hxt a).symm
    rw [ht, hinv, ← RingHom.map_mulVec]
    refine Formalism.MainNotions.Gaps.Loc.fst_int w φ halg _ ((hB _).1 ?_ a)
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx
  · refine ⟨_, (hB fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)).2
      fun a => Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (hu a), fun a => ?_⟩
    refine (RingHom.map_mulVec π _ _ a).trans ?_
    have : (π ∘ fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)) =
        ((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t := funext fun a => congrArg Prod.fst (halg _)
    rw [this]
    change ((bc π B).1 *ᵥ _) a = _
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

end GlobalTheory.PlaceOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisenstein
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRecip

theorem exists_frob_fix_of_eisenstein : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : G E Ω, IsFrob (F := E) A (normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  intro hG E Ω _ _ _ _ _ _ art hart v A hA ϖ hϖ hϖ2 π hπ
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional E (IntermediateField.adjoin E {π}) := IntermediateField.adjoin.finiteDimensional hint
  have : NumberField (IntermediateField.adjoin E {π}) := NumberField.of_module_finite E _
  have : IsAlgClosure (IntermediateField.adjoin E {π}) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  set K := IntermediateField.adjoin E {π} with hKdef
  obtain ⟨artK, hartK⟩ := hG K Ω
  obtain ⟨W, hWv, hWuniq, hAW, hnW, hunif⟩ := _root_.GlobalTheory.TameRecPlace.main E Ω v A hA ϖ hϖ hϖ2 π hπ
  obtain ⟨-, hnorm⟩ := GlobalTheory.TameEis.minpoly_and_norm_of_pow_eq_uniformizer E Ω v ϖ hϖ hϖ2 π hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have hv1 : (1 : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    rcases Nat.eq_zero_or_pos (normV v - 1) with h0 | h0
    · rw [h0, pow_zero] at hπ
      have : (ϖ : E) = ((1 : 𝓞 E) : E) := by
        apply (algebraMap E Ω).injective; rw [← hπ]; simp
      exact hv1 (by rw [← (RingOfIntegers.coe_injective this)]; exact hϖ)
    · rw [zero_pow h0.ne'] at hπ
      have : (ϖ : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hπ.symm
      exact hϖ2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.mp this]; exact Ideal.zero_mem _)
  have hgen0 : IntermediateField.AdjoinSimple.gen E π ≠ 0 := by
    intro h; apply hπ0
    have := congrArg (algebraMap K Ω) h
    simpa using this
  set yK : Kˣ := Units.mk0 _ hgen0 with hyK
  set cπ : (W.adicCompletion K)ˣ := Units.map (algebraMap K (W.adicCompletion K)).toMonoidHom yK with hcπ
  have hcu : IsUnifAt W cπ := hunif cπ rfl
  obtain ⟨σ, hσF, hσA⟩ := (hartK.frob W A hAW (artK (localIdele K W cπ))).mp ⟨cπ, hcu, rfl⟩
  have hN := GlobalTheory.T.artin_restrict_eq_artin_norm_single_place E Ω K art artK hart hartK v W hWv hWuniq yK σ⁻¹ hσA
  refine ⟨σ.restrictScalars E, ?_, ?_, ?_⟩
  · rw [← hnW]; exact hσF
  · have := σ.commutes (IntermediateField.AdjoinSimple.gen E π)
    simpa using this
  · intro c hc
    have hinv : (σ.restrictScalars E)⁻¹ = (σ⁻¹).restrictScalars E := rfl
    rw [hinv, hN]
    congr 2
    ext
    rw [hc]
    simp only [Units.coe_map, MonoidHom.coe_coe, hyK, Units.val_mk0]
    rw [hnorm]
    simp

end GlobalTheory.TameRecip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulMemSpan
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.LevLaws

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


omit [StarRing E] in
theorem exists_mul_mem_span (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal)
    (hq2 : q ∉ P.asIdeal ^ 2) : ∃ s ∉ P.asIdeal, ∀ r ∈ P.asIdeal, ∃ t, s * r = q * t := by
  have h1 : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨J, hJ⟩ := h1
  have h2 : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq2
    have : q ∈ P.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self q
    rw [sq]
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hsP⟩ := SetLike.not_le_iff_exists.1 h2
  refine ⟨s, hsP, fun r hr => ?_⟩
  have : r * s ∈ Ideal.span {q} := hJ ▸ Ideal.mul_mem_mul hr hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨t, by rw [mul_comm s r, ← ht, mul_comm]⟩

end Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

end GlobalTheory.Mem.Col2.LevLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePowSmulLeOfLocalizationsEqAway
section
noncomputable section

namespace GlobalTheory.InertExchange

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col

theorem exists_smul_mem_of_fg {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) (A B : Submodule R M) (hA : A.FG)
    (h : ∀ x ∈ A, ∃ s ∈ S, s • x ∈ B) : ∃ s ∈ S, ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨G, rfl⟩ := hA
  have key : ∀ G' : Finset M, (G' : Set M) ⊆ G → ∃ s ∈ S, ∀ x ∈ Submodule.span R (G' : Set M), s • x ∈ B := by
    intro G'
    induction G' using Finset.induction_on with
    | empty => exact fun _ => ⟨1, S.one_mem, fun x hx => by
        simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
        simp [hx]⟩
    | insert a G' _ ih =>
      intro hsub
      simp only [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨t, ht, hta⟩ := h a (Submodule.subset_span hsub.1)
      obtain ⟨s, hs, hsG⟩ := ih hsub.2
      refine ⟨t * s, S.mul_mem ht hs, fun x hx => ?_⟩
      rw [Finset.coe_insert, Submodule.mem_span_insert] at hx
      obtain ⟨r, y, hy, rfl⟩ := hx
      have e : (t * s) • (r • a + y) = (r * s) • (t • a) + t • (s • y) := by
        simp only [smul_add, smul_smul, mul_comm, mul_assoc, mul_left_comm]
      rw [e]
      exact B.add_mem (B.smul_mem _ hta) (B.smul_mem _ (hsG y hy))
  exact key G subset_rfl

private theorem infinite_places (E : Type) [Field E] [NumberField E] :
    Infinite (HeightOneSpectrum (𝓞 E)) := by
  have : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_surjective _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).surjective
  refine Infinite.of_surjective (fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 ℚ)) fun v => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
    HeightOneSpectrum.ext hl.over.symm⟩

theorem exists_smul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (B : Submodule (𝓞 E) (Sp E n)) (hB : Submodule.IsFullLattice E B) (x : Sp E n) :
    ∃ r ∈ nonZeroDivisors (𝓞 E), r • x ∈ B :=
  _root_.GlobalTheory.SmulMemOfIsLattice.exists_smul_mem_of_isLattice B hB x

theorem exists_pow_smul_le_of_localization_eq {E : Type} [Field E] [NumberField E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)) (hA : A.FG)
    (hB : Submodule.IsLattice E B)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) :
    ∃ k : ℕ, P.asIdeal ^ k • A ≤ B := by
  set I : Ideal (𝓞 E) := B.colon (A : Set (Sp E n)) with hIdef
  have hI0 : I ≠ ⊥ := by
    letI := infinite_places E
    obtain ⟨Q, hQ⟩ := exists_ne P
    obtain ⟨s, hs, hsA⟩ := exists_smul_mem_of_fg Q.asIdeal.primeCompl A B hA (fun x hx => by
      have hxA : x ∈ localization₂ Q.asIdeal A := ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using hx⟩
      rw [h Q hQ] at hxA
      exact hxA)
    intro hI
    have hsI : s ∈ I := Submodule.mem_colon.2 hsA
    rw [hI, Ideal.mem_bot] at hsI
    exact hs (hsI ▸ Q.asIdeal.zero_mem)
  have hIQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → ¬ I ≤ Q.asIdeal := by
    intro Q hQ hle
    obtain ⟨s, hs, hsA⟩ := exists_smul_mem_of_fg Q.asIdeal.primeCompl A B hA (fun x hx => by
      have hxA : x ∈ localization₂ Q.asIdeal A := ⟨1, Q.asIdeal.primeCompl.one_mem, by simpa using hx⟩
      rw [h Q hQ] at hxA
      exact hxA)
    exact hs (hle (Submodule.mem_colon.2 hsA))
  have hrad : P.asIdeal ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hIJ, hJ⟩
    by_cases hJ0 : J = ⊥
    · exact absurd (le_bot_iff.1 (hJ0 ▸ hIJ)) hI0
    · let Q : HeightOneSpectrum (𝓞 E) := ⟨J, hJ, hJ0⟩
      by_cases hQ : Q = P
      · have : Q.asIdeal = P.asIdeal := by rw [hQ]
        exact le_of_eq this.symm
      · exact absurd hIJ (hIQ Q hQ)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨k, Submodule.smul_le.2 fun r hr x hx => Submodule.mem_colon.1 (hk hr) x hx⟩

theorem exists_pow_smul_le_of_locP_eq :
    ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
      (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B →
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) →
      ∃ k : ℕ, P.asIdeal ^ k • A ≤ B ∧ P.asIdeal ^ k • B ≤ A := by
  intro E _ _ _ n P A B hA hB h
  obtain ⟨k₁, h₁⟩ := exists_pow_smul_le_of_localization_eq P A B hA.fg hB h
  obtain ⟨k₂, h₂⟩ := exists_pow_smul_le_of_localization_eq P B A hB.fg hA (fun Q hQ => (h Q hQ).symm)
  refine ⟨max k₁ k₂, ?_, ?_⟩
  · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_left k₁ k₂))).trans h₁
  · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right k₁ k₂))).trans h₂

end GlobalTheory.InertExchange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.StepOk

theorem finite_orbits_of_finite_fibres {G A B : Type} [Group G] [MulAction G A] [MulAction G B] (π : A → B)
    (hπ : ∀ (g : G) a, π (g • a) = g • π a) (hf : ∀ b, {a | π a = b}.Finite)
    [Finite (MulAction.orbitRel.Quotient G B)] : Finite (MulAction.orbitRel.Quotient G A) := by
  haveI : ∀ b, Finite {a | π a = b} := fun b => (hf b).to_subtype
  refine Finite.of_surjective (fun x : Σ q : MulAction.orbitRel.Quotient G B, {a | π a = q.out} =>
    (Quotient.mk _ x.2.1 : MulAction.orbitRel.Quotient G A)) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h a =>
    have h : (MulAction.orbitRel G B).r (Quotient.mk (MulAction.orbitRel G B) (π a)).out (π a) :=
      Quotient.exact (Quotient.out_eq _)
    obtain ⟨g, hg⟩ := h
    refine ⟨⟨Quotient.mk _ (π a), ⟨g • a, (hπ g a).trans hg⟩⟩, ?_⟩
    exact Quotient.sound ⟨g, rfl⟩

theorem ufGL_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) (x : Fin n → E) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

theorem ufGL_conjTranspose_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᴴ *
      ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
  ext a b
  have h : ∑ i, star (γ.1 (Pi.single a 1) i) * γ.1 (Pi.single b 1) i =
      ∑ i, star ((Pi.single a 1 : Fin n → E) i) * (Pi.single b 1 : Fin n → E) i :=
    γ.2 (Pi.single a 1) (Pi.single b 1)
  have hv : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
    LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) := rfl
  rw [hv, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rw [Finset.sum_eq_single a]
    · simp [Matrix.one_apply, Pi.single_apply]
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem levQ_root (Θ : LevQFam X.E X.K n Q) (h : ∀ P g, ∃ m : ℕ, 0 < m ∧ (Θ P).lam g ^ m = 1) (g : Θ.grp) :
    ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1 := by
  rw [← isOfFinOrder_iff_pow_eq_one]
  unfold LevQFam.chr piChar
  erw [MonoidHom.finsetProd_apply]
  refine Finset.prod_induction _ IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one fun P _ => ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact h P _

theorem eq_one_of_fst (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (g : FrmG Λ Θ)
    (hg : FrmG.incl Λ Θ g • p = p) (h1 : g.1 = 1) : g = 1 := by
  have hb : FrmG.incl Λ Θ 1 • p = p := by rw [map_one, one_smul]
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1))
    (b := ((FrmG.incl Λ Θ 1).1, (FrmG.incl Λ Θ 1).2.1)) (congrArg DecoF.deco hg) (congrArg DecoF.deco hb) h1
  exact FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p hg hb h1 (Prod.mk.inj h2).2)

theorem stepY_ok : ∀ {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q), X.Ok → ∀ (ST : Finset (HeightOneSpectrum (𝓞 X.E))) (pref : DecoF X.E n ST SG Q → Prop), (∀ b P, (Θ b P).H.FiniteIndex) → (∀ b P g, ∃ m : ℕ, 0 < m ∧ (Θ b P).lam g ^ m = 1) → (∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) → (stepY ST y β Λ Θ pref).Ok := by
  intro X n SG Q y β _ _ Λ Θ hX ST pref hfi hroot hfin
  have hG := fun b => FramedForms.main hX (ST := ST) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (Λ b) (Θ b) (hfi b)
    (levQ_root (Θ b) (hroot b))
  refine ⟨fun b => ?_, fun b p => ?_, fun b g => ?_, fun b g => ?_, fun b g p x => ?_, fun b p => ?_, fun b g p hg h1 => ?_⟩
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.orbitRel.Quotient (FrmG (Λ b) (Θ b)) (DecoF X.E n ST SG Q)) := (hG b).fin_orb
    refine finite_orbits_of_finite_fibres (G := FrmG (Λ b) (Θ b)) (A := PtY ST SG Q y) (B := DecoF X.E n ST SG Q)
      (fun p => p.1.1) (fun _ _ => rfl) fun d => ?_
    refine Set.Finite.of_finite_image (f := fun p : PtY ST SG Q y => p.1.2) ?_ ?_
    · refine (hfin d.deco.1.N d.deco.2.1).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p.1.1 = d := hp
      rw [← hp']
      exact p.2
    · intro p hp q hq h
      exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1) := (hG b).fin_stab p.1.1
    refine Finite.of_injective (fun a : MulAction.stabilizer (FrmG (Λ b) (Θ b)) (show PtY ST SG Q y from p) =>
      (⟨a.1, congrArg (fun q : PtY ST SG Q y => q.1.1) a.2⟩ : MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1)) ?_
    intro a c h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  · exact ufGL_conjTranspose_mul g.1
  · obtain ⟨m, hm, hc⟩ := FramedForms.chr_root (Λ b) (Θ b) (levQ_root (Θ b) (hroot b)) g
    exact ⟨m, hm, Units.ext ((Units.val_pow_eq_pow_val _ _).trans hc)⟩
  · have h := p.1.1.deco.1.Lsh_act g.1.2 g.2.1.1
    show ((ufGL X.E n g.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [h, ufGL_mulVec, mem_gmap, LinearEquiv.symm_apply_apply]
  · exact p.1.1.deco.2.Lsh_full_lattice
  · refine eq_one_of_fst (Λ b) (Θ b) p.1.1 g (congrArg (fun q : PtY ST SG Q y => q.1.1) hg) ?_
    have h2 : ufGL X.E n g.1 = 1 := h1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [← ufGL_mulVec, h2]
    simp

end GlobalTheory.Mem.Col2.StepOk
end

