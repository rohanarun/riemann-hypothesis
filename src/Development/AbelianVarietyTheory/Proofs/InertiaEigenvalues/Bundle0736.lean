module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadingOver

open GlobalTheory.GoodPts

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

theorem norm_le_one_of_valuation_le_one {x : F} (hx : (placeAt φ).valuation F x ≤ 1) : ‖φ x‖ ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact norm_int_le_one φ n

variable (T : CDVR)

theorem valV_le_one_of_inV {x : T.Fr} (hx : InV T x) : valV T.V x ≤ 1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem inV_of_valV_le_one {x : T.Fr} (hx : valV T.V x ≤ 1) : InV T x := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
    (IsDiscreteValuationRing.maximalIdeal T.V) x hx
  have hu : IsUnit (d : T.V) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  refine ⟨n * ↑hu.unit⁻¹, ?_⟩
  rw [map_mul, ← hnd, mul_assoc, ← map_mul, hu.mul_val_inv, map_one, mul_one]

theorem vV_zpow {x : T.Fr} (n : ℤ) : vV T.V (x ^ n) = n * vV T.V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

variable {T}

theorem overLa_placeAt_of_isReading {io : F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (hR : IsReading φ T io k) :
    ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  set P := placeAt φ with hP
  have key : ∀ y : T.Fr, valV T.V y ≤ 1 ↔ ‖k y‖ ≤ 1 := fun y =>
    ⟨fun h => (hR.int y).2 (inV_of_valV_le_one T h), fun h => valV_le_one_of_inV T ((hR.int y).1 h)⟩
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖φ (π : F)‖ < 1 := (mem_placeAt φ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    have h' : π = 0 := by exact_mod_cast h
    rw [h', map_zero] at hπ
    exact WithZero.exp_ne_zero.symm hπ
  have hνπ : P.valuation F (π : F) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  set x := io (π : F) with hx
  have hx0 : x ≠ 0 := (map_ne_zero io).2 hπ0
  have hkx : ‖k x‖ < 1 := by rw [hx, hR.comp]; exact hπn
  have hvx1 : valV T.V x < 1 := by
    refine lt_of_le_of_ne ((key x).2 hkx.le) fun h1 => ?_
    have h2 : valV T.V x⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
    have h3 := (key _).1 h2
    rw [map_inv₀, norm_inv] at h3
    have h4 : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 hx0)
    exact absurd h3 (not_le.2 ((one_lt_inv₀ h4).2 hkx))
  have hvx : 0 < vV T.V x := by
    have h := (WithZero.log_lt_log (valV_ne_zero hx0) one_ne_zero).2 hvx1
    rw [WithZero.log_one] at h
    simp only [vV]; omega
  refine ⟨(vV T.V x).toNat, by omega, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  set n := vLa P a with hn
  set b := a * (π : F) ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hπ0)
  have hνa : P.valuation F a = WithZero.exp (-n) := by
    rw [hn, vLa, neg_neg, WithZero.exp_log ((P.valuation F).ne_zero_iff.2 ha)]
  have hνb : P.valuation F b = 1 := by
    rw [hb, map_mul, map_zpow₀, hνa, hνπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hkb : ‖k (io b)‖ ≤ 1 := by rw [hR.comp]; exact norm_le_one_of_valuation_le_one φ hνb.le
  have hkb' : ‖k (io b)⁻¹‖ ≤ 1 := by
    rw [← map_inv₀, hR.comp]
    exact norm_le_one_of_valuation_le_one φ (by rw [map_inv₀, hνb, inv_one])
  have hvb1 : valV T.V (io b) = 1 := by
    have h1 := (key _).2 hkb
    have h2 := (key _).2 hkb'
    rw [map_inv₀] at h2
    have hv0 : valV T.V (io b) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hb0)
    have h3 : valV T.V (io b) * (valV T.V (io b))⁻¹ ≤ valV T.V (io b) * 1 := mul_le_mul_right h2 _
    rw [mul_inv_cancel₀ hv0, mul_one] at h3
    exact le_antisymm h1 h3
  have hvb : vV T.V (io b) = 0 := by simp [vV, hvb1]
  have hab : io a = io b * x ^ n := by
    rw [hx, ← map_zpow₀, ← map_mul, hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hab, vV_mul ((map_ne_zero io).2 hb0) (zpow_ne_zero _ hx0), hvb, vV_zpow, Int.toNat_of_nonneg hvx.le]
  ring

theorem overLa_placeAt : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e :=
  fun _ _ _ _ _ φ _ _ _ hR => overLa_placeAt_of_isReading φ hR

end GlobalTheory.ReadingOver

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubquotientJacquetModuleOfSupercuspidalSup
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.CuspQuot

theorem stage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (GlobalTheory.SmGL.jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (GlobalTheory.SmGL.jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (GlobalTheory.SmGL.jac E π) := _root_.GlobalTheory.JacStages.isSubquotient_jac_refine

theorem degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (GlobalTheory.SmGL.jac e π) := _root_.GlobalTheory.piTensor_isSubquotient_jac_degZero

theorem oneBlock : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (GlobalTheory.SmGL.jac e π) := _root_.GlobalTheory.SingleBlockJac.isSubquotient_piTensor_jac

open GlobalTheory.Published GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (hZ : ZelevinskyPolynomialRing) (N : ℕ) :
    ∀ (x : IrrGL (k := k)), x.1 = N → ∀ s : Multiset (IrrGL (k := k)), HasSupport x.rep s →
      ∃ (r : ℕ) (u : Fin r → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin x.1),
        (∀ a, u a ∈ s) ∧ IsSubquotient (piTensor fun a => (u a).rep) (GlobalTheory.SmGL.jac e x.rep) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s hs
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · haveI : IsEmpty (Fin x.1) := by rw [h0]; infer_instance
      exact ⟨0, Fin.elim0, Equiv.equivOfIsEmpty _ _, fun a => a.elim0,
        degZero k x.1 h0 _ x.rep _ _ _ _⟩
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs]
      exact ⟨1, fun _ => x, GlobalTheory.JacTensor.oneBlock x.1, fun _ => Multiset.mem_singleton_self x,
        oneBlock k x.1 _ x.rep _⟩
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (GlobalTheory.SmGL.jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨t, ht, rfl⟩ := exists_sum_of_jac hG hZ hs e hτ hτs y hy
    have hlt : ∀ j, d j < x.1 := by
      intro j
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    let z : Fin r → IrrGL (k := k) := fun j => IrrGL.of (y j).ρ (y j).smooth (y j).irr
    have hrec := fun j => ih (d j) (hlt j) (z j) rfl (t j) ((ht j).of_equiv (IrrGL.equivOf _ _ _))
    choose T u E hu hsub using hrec

    let πI : GlobalTheory.SplitRead.Irr k x.1 := ⟨x.2.rep.V, x.rep, x.2.rep.smooth, x.2.rep.irr⟩
    obtain ⟨σ, hσ⟩ := GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k x.1 πI r d e Y τ hτ hτs
    have hSch : ∀ a, ∀ φ : (σ a).V →ₗ[ℂ] (σ a).V, (∀ g v, φ ((σ a).π g v) = (σ a).π g (φ v)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
      GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin (d a))) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (σ a).V (σ a).π (σ a).irr ((hBZ k).1 (Fin (d a)) (σ a).V (σ a).π (σ a).smooth (σ a).irr)
    have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
      GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (σ a).irr) hSch
    obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient hτ hirr hσ
    have hyσ : ∀ j, Nonempty ((σ j).π.Equiv (y j).ρ) := fun j =>
      nonempty_equiv_of_isSubquotient (y j).irr (σ j).irr
        (isSubquotient_factor (fun a => (σ a).π) j (y j).irr ((hy j).trans
          (isSubquotient_comp (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) _)))
    have ψ := fun j => (hyσ j).some
    let χ : (piTensor fun j => (z j).rep).Equiv τ :=
      (piTensorEquiv fun j => ((ψ j).trans (IrrGL.equivOf (y j).ρ (y j).smooth (y j).irr)).symm).trans φ
    have hz : IsSubquotient (piTensor fun j => (z j).rep) (GlobalTheory.SmGL.jac e x.rep) :=
      (IsSubquotient.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective).trans hτs
    obtain ⟨E', hE'⟩ := stage k x.1 r d e _ x.rep x.2.rep.smooth _ (fun j => (z j).rep) (fun j => (z j).2.rep.smooth) hz
      T (fun a b => (u a b).1) E _ (fun a b => (u a b).rep) hsub
    refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E', fun c => ?_, hE'⟩
    exact Multiset.mem_of_le (Finset.single_le_sum (f := t) (fun _ _ => Multiset.zero_le _)
      (Finset.mem_univ (finSigmaFinEquiv.symm c).1)) (hu _ _)

theorem exists_isSubquotient_jac_of_hasSupport : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))), HasSupport x.rep s → ∃ (r : ℕ) (u : Fin r → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin x.1), (∀ a, u a ∈ s) ∧ IsSubquotient (piTensor fun a => (u a).rep) (GlobalTheory.SmGL.jac e x.rep) :=
  fun hG hBZ hZ _ _ _ _ _ _ x s hs => finiteRing_sq_sub_mul_sq_eq_of_card hG hBZ hZ x.1 x rfl s hs

end GlobalTheory.CuspQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

def quo : (AE D)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  MonoidHom.mk' (fun x => Units.map (finPart D).toMonoidHom x *
      (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹)
    (fun x y => by simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _)

theorem quo_mul (x : (AE D)ˣ) :
    ((quo D x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D) := by
  have hsv : ((Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := GlobalTheory.DetRootChar.finPart_sigR D x
  rw [← hsv]
  show ((Units.map (finPart D).toMonoidHom x * (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹ :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) * _ = _
  rw [← Units.val_mul, inv_mul_cancel_right]
  rfl

theorem quo_eq_of (x : (AE D)ˣ) (u : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)
    (hu : (u : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) =
      finPart D (x : AE D)) : quo D x = u := by
  set s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
    Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x with hs
  have hsv : (s : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hs]; exact GlobalTheory.DetRootChar.finPart_sigR D x
  have h1 := quo_mul D x
  rw [← hsv] at h1 hu
  have : ((quo D x * s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)) = u * s := Units.ext (by simp [h1, hu])
  exact mul_right_cancel this

theorem ker_trivial (δ : (AE D)ˣ →* Circle) (hF : ∀ a, δ (idF D a) = 1) (hfin : ∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1)
    (x : (AE D)ˣ) (hx : quo D x = 1) : δ x = 1 := by
  have h1 := quo_mul D x
  rw [hx, Units.val_one, one_mul] at h1
  obtain ⟨a, y, hy, hxy⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x h1
  obtain ⟨m, hm, hδ⟩ := hfin
  obtain ⟨z, hz⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D m hm y hy
  rw [hxy, map_mul, hF, mul_one, ← hz, map_pow, hδ]

theorem quo_of_isDetRoot (W : HSp D) (g : GA D W) (x : (AE D)ˣ) (hx : IsDetRoot W g x) :
    quo D x = Matrix.GeneralLinearGroup.det (finHom W g) := by
  apply quo_eq_of
  have hdet : ((Matrix.GeneralLinearGroup.det (finHom W g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      Af D.host.F ⊗[D.host.F] D.host.E) = finPart D (matHom W g).1.det :=
    (GlobalTheory.DetRootChar.finPart_det D W g).symm
  rw [hdet, ← GlobalTheory.DetRootChar.finPart_sigR, ← RingHom.map_mul]
  exact (congrArg _ hx).symm

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

theorem val_of_quo (χ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* Circle) (Y : (AE D)ˣ) :
    (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((χ (quo D Y) : Circle) : ℂ) := by
  simp

theorem exists_rat (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (a : D.host.E)
    (hxa : (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 ⊗ₜ a) (hx : GlobalTheory.FinalJoin.NormOne x)
    [Nontrivial (Af D.host.F)] : ∃ w : D.host.Eˣ, quo D (Units.map (incA D).toMonoidHom w) = x := by
  have hN : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  rw [hxa] at hN
  have ha : a * D.sp.cm.sig a = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (A := Af D.host.F) (R := D.host.F)
      (algebraMap D.host.F (Af D.host.F)).injective
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] (a * D.sp.cm.sig a) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [← Algebra.TensorProduct.one_def]
    simpa [sigR] using hN
  have hu : a ∈ unitary D.host.E := ⟨by rw [mul_comm]; exact ha, ha⟩
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.NormOneHilbert90Units.exists_ne_zero_mul_conj_eq_of_unitary D ⟨a, hu⟩
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply quo_eq_of
  have hfY : finPart D ((Units.map (incA D).toMonoidHom (Units.mk0 w hw0) : (AE D)ˣ) : AE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] w := rfl
  rw [hfY, hxa]
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj] at hw
  exact congrArg _ hw

theorem exists_cong (N : ℕ) (hN : Odd N) (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x)
    (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (hwe : (x : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = N • w) :
    ∃ Y : (AE D)ˣ, FinUnit Y ∧ (∃ y ∈ intAE D, finPart D (Y : AE D) - 1 = N • y) ∧ quo D Y = x := by
  have hn : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  obtain ⟨y, y', hy, hy', hyy, hroot, q, hq, hqe⟩ :=
    _root_.GlobalTheory.OddRoot.exists_root_odd D N hN (x : Af D.host.F ⊗[D.host.F] D.host.E) w hw hwe hn
  obtain ⟨Y, h1, h2, h3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨h1, h2 ▸ hy, h3 ▸ hy'⟩, ⟨q, hq, h2 ▸ hqe⟩, ?_⟩
  apply quo_eq_of
  rw [h2]
  exact hroot.symm

theorem exists_normOne (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x) :
    ∃ Y : (AE D)ˣ, quo D Y = x := by
  obtain ⟨y, hy⟩ := (GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D).1 x hx
  obtain ⟨Y, -, h1, -⟩ := GlobalTheory.DetRootCong.exists_idele D (y : Af D.host.F ⊗[D.host.F] D.host.E)
    ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) y.mul_inv
  have hc : ((Formalism.L2.Pj.cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.IdeleNinety.coe_cjFin D y
  refine ⟨Y, ?_⟩
  apply quo_eq_of
  rw [h1, ← hc, hy, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

theorem read_anticyc : ∀ (D : D7) (W : HSp D) (L : Type) [Field L] (σ : L →+* ℂ) (p : ℕ), Odd p → ∀ δ : (AE D)ˣ →* Circle, IsHeckeChar D δ → (∀ a, δ (Formalism.L2.Theta.idF D a) = 1) → (∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1) → (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = p • y) → δ x = 1) → (∀ x, ∃ y : L, σ y = ((δ x : Circle) : ℂ)) → ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ p xi ∧ ∀ (g : GA D W) (x : (AE D)ˣ), IsDetRoot W g x → ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) = ((δ x : Circle) : ℂ) := by
  intro D W L _ σ p hp δ hH hF hfin hcong hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.DetRootChar.circle_hom_factor (quo D) δ (ker_trivial D δ hF hfin)
  have hxi : ∀ Y : (AE D)ˣ, (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((δ Y : Circle) : ℂ) := by
    intro Y
    rw [val_of_quo, hχ]
  refine ⟨Circle.toUnits.comp χ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x a hxa hx
    rcases subsingleton_or_nontrivial (Af D.host.F) with hs | hs
    · have h0 : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul b e => rw [Subsingleton.elim b 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      have hx1 : x = 1 := Units.ext ((h0 _).trans (h0 _).symm)
      rw [hx1, map_one]
    obtain ⟨w, hw⟩ := exists_rat D x a hxa hx
    apply Units.ext
    rw [← hw, hxi, hH.2 w]
    rfl
  · rintro x hx ⟨w, hw, hwe⟩
    obtain ⟨Y, hY, hYc, hQ⟩ := exists_cong D p hp x hx w hw hwe
    apply Units.ext
    rw [← hQ, hxi, hcong Y hY hYc]
    rfl
  · intro x hx
    obtain ⟨Y, hQ⟩ := exists_normOne D x hx
    obtain ⟨a, ha⟩ := hval Y
    refine ⟨a, ?_⟩
    rw [← hQ, hxi]
    exact ha
  · intro g x hx
    rw [← quo_of_isDetRoot D W g x hx, hxi]

end GlobalTheory.AntiCycRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniquePlaceBelowOfUnramifiedPlaceOverPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.InertiaEigenvalues.UnramPlace

theorem exists_place_below : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (l : ℕ), l.Prime → ∀ la : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.UnramAt φ {la} → ∃ p : HeightOneSpectrum (𝓞 K), GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below φ {la} = {p} ∧ ((l : ℕ) : 𝓞 K) ∈ p.asIdeal ∧ ∀ x : K, la.valuation L (φ x) = p.valuation K x := by
  intro K L _ _ _ _ φ l _ la hl hun
  letI : Algebra K L := φ.toAlgebra
  have hmap : RingOfIntegers.mapRingHom φ = algebraMap (𝓞 K) (𝓞 L) := by
    ext x; rfl
  refine ⟨la.under (𝓞 K), ?_, ?_, ?_⟩
  · ext q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.below, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
    rw [hmap]
    exact ⟨fun h => HeightOneSpectrum.ext h, fun h => h ▸ rfl⟩
  · show ((l : ℕ) : 𝓞 K) ∈ la.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
    rw [Ideal.mem_comap, map_natCast]
    exact hl
  · intro x
    have hu := hun la rfl
    rw [hmap] at hu
    have : la.asIdeal.LiesOver (la.under (𝓞 K)).asIdeal := ⟨rfl⟩
    have he : (la.under (𝓞 K)).asIdeal.ramificationIdx' la.asIdeal = 1 := by
      refine Ideal.ramificationIdx'_spec ?_ ?_
      · rw [pow_one]; exact Ideal.map_comap_le
      · exact hu
    have h := HeightOneSpectrum.valuation_liesOver L (la.under (𝓞 K)) la x
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (la.under (𝓞 K)).ne_bot, he, pow_one] at h
    exact h.symm

end GlobalTheory.InertiaEigenvalues.UnramPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFrameConjUnitaryIntegralIffGLIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFrame_conj_unitaryIntegral_iff_GL_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ x, (p x ∈ Formalism.UG.KU σ n ↔ cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n)) := by
  first | exact @GlobalTheory.KUTransfer.ku_iff | exact GlobalTheory.KUTransfer.ku_iff | (intros; apply GlobalTheory.KUTransfer.ku_iff <;> assumption)
end

