module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.SphSupport

open ValuativeRel Cardinal

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_one_comm (x y : GL (Fin 1) k) : x * y = y * x := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem levi_comm {m : ℕ} (g h : Levi k (fun _ : Fin m => Fin 1)) : g * h = h * g :=
  funext fun a => gl_one_comm (g a) (h a)

theorem scalar_det_fin_one (g : GL (Fin 1) k) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g) = g := by
  apply Units.ext
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_one]

theorem det_scalar_fin_one (z : kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) z) = z := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem mk_ne_zero (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hχ : IsSmoothChar χ) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y)
    {s : ℕ} (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin m) :
    (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) ≠ 0 := by
  intro h0
  let σ' : Representation ℂ (GL (Fin m) k) V := twist σ (detChar (Fin m) χ⁻¹)
  let π : Irr k m := ⟨V, σ', isSmooth_twist hs hχ.inv.detChar, GlobalTheory.LocGL.isIrreducible_twist hi _⟩
  have hker : twKer σ' (unipRad k e) 1 = twKer σ (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor <;> rintro ⟨u, v, rfl⟩ <;> refine ⟨u, v, ?_⟩ <;>
      simp [σ', det_eq_one_of_mem_unipRad k u.2]
  have hle : KOne k (Fin m) ⊔ (unipRad k e ⊓ KO k (Fin m)) ≤ KO k (Fin m) :=
    sup_le (Subgroup.map_le_range _ _) inf_le_right
  refine hy (hD k m s d e π y ?_ ?_)
  · intro h
    have hKO := hle h.2
    show σ' h y = _
    simp only [σ', twist_apply, detChar_apply, hK _ hKO, smul_smul, MonoidHom.inv_apply]
    simp
  · show (Submodule.Quotient.mk y : V ⧸ twKer σ' (unipRad k e) 1) = 0
    rw [Submodule.Quotient.mk_eq_zero, hker]
    exact (Submodule.Quotient.mk_eq_zero _).1 h0

theorem inSupport_of_KO_eigen (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V) (hs : IsSmooth σ)
    (hi : σ.IsIrreducible) (hχ : IsSmoothChar χ) (hm : 0 < m) (hy : y ≠ 0)
    (hK : ∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) :
    ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  let e : (Σ _ : Fin m, Fin 1) ≃ Fin m := Equiv.sigmaUnique (Fin m) fun _ => Fin 1
  have hy' := mk_ne_zero hD σ χ y hs hi hχ hy hK (fun _ : Fin m => 1) e
  let a0 : Fin m := ⟨0, hm⟩
  let S : Set (Levi k (fun _ : Fin m => Fin 1)) :=
    {g | ∀ a, valuation k ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) = 1}
  let θ : Levi k (fun _ : Fin m => Fin 1) → ℂ := fun g =>
    (((deltaHalf k (fun _ : Fin m => Fin 1) g)⁻¹ : ℂˣ) : ℂ) *
      (χ (Matrix.GeneralLinearGroup.det (leviEmb k e g)) : ℂ)
  have hKOlevi : ∀ g ∈ S, leviEmb k e g ∈ KO k (Fin m) := by
    intro g hg
    have h1 : leviEmb k e g = diagT k (Fin m) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
      conv_lhs => rw [GlobalTheory.EigenSupport.eq_torusToLevi m g]
      exact GlobalTheory.SmGL.EmptyBlocks.leviEmb_torusToLevi k e _
    rw [h1]
    exact iwahori_le_KO k (Fin m) (diagT_mem_iwahori (t := fun j => Matrix.GeneralLinearGroup.det (g j)) hg)
  have hδ : ∀ g ∈ S, deltaHalf k (fun _ : Fin m => Fin 1) g = 1 := by
    intro g hg
    rw [deltaHalf_apply]
    exact Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ (hg a)
  have hθ : ∀ g ∈ S, GlobalTheory.SmGL.jac e σ g (Submodule.Quotient.mk y) = θ g • (Submodule.Quotient.mk y : Jacquet σ (unipRad k e)) := by
    intro g hg
    rw [jac_mk, hK _ (hKOlevi g hg), Submodule.Quotient.mk_smul, smul_smul]
  obtain ⟨Y, _, _, τ, hτi, hτs, y₀, hy₀, hy₀θ⟩ :=
    GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen _ _ (GlobalTheory.SmGL.jac e σ) S θ _ hy' hθ
  have hrank : Module.rank ℂ Y ≤ ℵ₀ := by
    obtain ⟨S', f, hf⟩ := hτs
    haveI := GlobalTheory.LocGL.secondCountableTopology_GL k (Fin m)
    exact (LinearMap.rank_le_of_surjective f.toLinearMap hf).trans ((Submodule.rank_le _).trans
      ((LinearMap.rank_le_of_surjective _ (Submodule.mkQ_surjective _)).trans (GlobalTheory.LocGL.rank_le_aleph0_of_isIrreducible hs hi)))
  have hc : ∀ g : GL (Fin 1) k, ∃ c : ℂ, ∀ w, τ (Pi.mulSingle a0 g) w = c • w := fun g =>
    GlobalTheory.LocGL.exists_eq_smul_of_rank_le hτi hrank ⟨τ (Pi.mulSingle a0 g), fun h => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, levi_comm]⟩
  choose c hc using hc
  have hc1 : c 1 = 1 := smul_left_injective ℂ hy₀ (by
    show c 1 • y₀ = (1 : ℂ) • y₀
    rw [← hc, Pi.mulSingle_one, map_one, one_smul]; rfl)
  have hcmul : ∀ g h, c (g * h) = c g * c h := fun g h => smul_left_injective ℂ hy₀ (by
    show c (g * h) • y₀ = (c g * c h) • y₀
    rw [← hc, Pi.mulSingle_mul, map_mul, Module.End.mul_apply, hc h, hc g, smul_smul])
  let ω' : GL (Fin 1) k →* ℂˣ := MonoidHom.toHomUnits ⟨⟨c, hc1⟩, hcmul⟩
  let ω : kˣ →* ℂˣ := ω'.comp (Matrix.GeneralLinearGroup.scalar (Fin 1))
  have hω : ∀ u : kˣ, valuation k (u : k) = 1 → ω u = χ u := by
    intro u hu
    let g : Levi k (fun _ : Fin m => Fin 1) := Pi.mulSingle a0 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)
    have hg : g ∈ S := by
      intro a
      by_cases ha : a = a0
      · subst ha; simp [g, det_scalar_fin_one, hu]
      · simp [g, Pi.mulSingle_eq_of_ne ha]
    have hdet : Matrix.GeneralLinearGroup.det (leviEmb k e g) = u := by
      rw [det_leviEmb, Finset.prod_eq_single a0]
      · simp [g, det_scalar_fin_one]
      · intro b _ hb; simp [g, Pi.mulSingle_eq_of_ne hb]
      · simp
    have h1 := (hc _ y₀).symm.trans (hy₀θ g hg)
    simp only [θ, hδ g hg, hdet, inv_one, Units.val_one, one_mul] at h1
    exact Units.ext (smul_left_injective ℂ hy₀ h1)
  obtain ⟨α, hα⟩ := GlobalTheory.JacSuppCount.eq_mul_unrChar_of_eq_on_units k χ ω hω
  refine ⟨α, m, fun _ => 1, e, a0, rfl, Y, inferInstance, inferInstance, τ, hτi, hτs, fun g w => ?_⟩
  rw [← hα]
  show τ (Pi.mulSingle a0 g) w = c (Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det g)) • w
  rw [scalar_det_fin_one, hc]

end GlobalTheory.SphSupport

theorem GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  intro _ _ hD k _ _ _ _ m V _ _ σ χ y hs hi hχ hm hy hK
  exact GlobalTheory.SphSupport.inSupport_of_KO_eigen hD σ χ y hs hi hχ hm hy hK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorCompSphericalConvolution
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open GlobalTheory.SatInd

namespace GlobalTheory.InertConv

theorem eq_of_coset {G : Type} [Group G] {K : Subgroup G} {k : Type} {H : G → k}
    (hH : ∀ (a : G) (c : K), H (a * c) = H a) {a b : G} (hab : (a : G ⧸ K) = b) : H a = H b := by
  have hc := QuotientGroup.eq.1 hab
  have := hH a ⟨a⁻¹ * b, hc⟩
  change H (a * (a⁻¹ * b)) = H a at this
  rw [mul_inv_cancel_left] at this
  exact this.symm

theorem finsum_eq_of_support_subset_range {α β M : Type} [AddCommMonoid M] {F : α → M} {e : β → α}
    (he : Function.Injective e) (hs : Function.support F ⊆ Set.range e) :
    ∑ᶠ c, F c = ∑ᶠ d, F (e d) := by
  rw [← finsum_mem_range he, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs, finsum_mem_support]

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem conv_of (Dv : InertDatum L n v w) (U : Subgroup (GAf L n))
    (hU : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n))
    (hA : ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n)
    (hE : ∀ u ∈ Umax L n, ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) :
      Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L))
    (hC : ∀ y ∈ GU Dv.σw n, ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y)
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (h : GU Dv.σw n → ℂ) (hh : h ∈ Hecke ℂ (KU Dv.σw n))
    (h' : GU Dv.σw n → ℂ) (hh' : h' ∈ Hecke ℂ (KU Dv.σw n))
    (f : GAf L n → W) (hf : ∀ κ ∈ U, NG.rt L n κ f = f) :
    heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f =
      heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  classical
  set K := KU Dv.σw n with hKdef
  let lam : GAf L n →* GU Dv.σw n := MonoidHom.codRestrict (GlobalTheory.SatInd.CosetFin.locHom Dv) _ hA
  have hlam : ∀ x, ((lam x : GU Dv.σw n) : GL (Fin n) (w.adicCompletion L)) = Dv.loc x := fun _ => rfl
  have hK1 : ∀ u ∈ Umax L n, lam u ∈ K := by
    intro u hu
    refine GlobalTheory.SatInd.DCoset.mem_KU_of_entries (lam u) (fun i j => hE u hu i j) (fun i j => ?_)
    rw [← map_inv]
    exact hE u⁻¹ (inv_mem hu) i j
  have hR : ∀ x x' : GAf L n, TrivOutside {v} x → TrivOutside {v} x' →
      ((x : GAf L n ⧸ U) = x' ↔ ((lam x : GU Dv.σw n ⧸ K) = lam x')) := by
    intro x x' hx hx'
    have ht : TrivOutside {v} (x⁻¹ * x') :=
      GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_inv hx) hx'
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
    constructor
    · intro hu; exact hK1 _ ((hU _ ht).1 hu)
    · intro hk
      exact (hU _ ht).2 (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv _ ht fun i j => GlobalTheory.SatInd.CosetFin.entries_int hk i j)
  have hCs : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, TrivOutside {v} x ∧ lam x = d.out := fun d => by
    obtain ⟨x, hx, e⟩ := hC _ d.out.2
    exact ⟨x, hx, Subtype.ext e⟩
  choose s hs1 hs2 using hCs
  have heT : ∀ d : GU Dv.σw n ⧸ K, ∃ x : GAf L n, (x : GAf L n ⧸ U) = (s d : GAf L n ⧸ U) ∧
      TrivOutside {v} x := fun d => ⟨s d, rfl, hs1 d⟩
  have hρ1 : ∀ d, TrivOutside {v} (heT d).choose := fun d => (heT d).choose_spec.2
  have hρ2 : ∀ d, ((lam (heT d).choose : GU Dv.σw n) : GU Dv.σw n ⧸ K) = d := fun d => by
    rw [(hR _ _ (hρ1 d) (hs1 d)).1 (heT d).choose_spec.1, hs2 d, QuotientGroup.out_eq']
  have he : Function.Injective (fun d : GU Dv.σw n ⧸ K => ((s d : GAf L n) : GAf L n ⧸ U)) := by
    intro d d' hdd
    have := (hR _ _ (hs1 d) (hs1 d')).1 hdd
    rwa [hs2, hs2, QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

  have step2 : ∀ (H : GU Dv.σw n → ℂ), (∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a) →
      ∀ (F : GAf L n → W) (g : GAf L n),
      heckeFunI L n U Dv H F g = ∑ᶠ d : GU Dv.σw n ⧸ K, H d.out • F (g * (heT d).choose) := by
    intro H hH F g
    show (∑ᶠ c : GAf L n ⧸ U, _) = _
    rw [finsum_eq_of_support_subset_range he]
    · refine finsum_congr fun d => ?_
      rw [dite_eq_left (heT d)]
      have hv : Dv.hval H (Dv.loc (heT d).choose) = H d.out := by
        rw [InertDatum.hval, dite_eq_left (hA _)]
        exact eq_of_coset hH (by rw [QuotientGroup.out_eq']; exact hρ2 d)
      rw [hv]
    · intro c hc
      rw [Function.mem_support] at hc
      by_cases hT : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · obtain ⟨x, hxc, hx⟩ := hT
        refine ⟨(lam x : GU Dv.σw n ⧸ K), ?_⟩
        show ((s _ : GAf L n) : GAf L n ⧸ U) = c
        rw [← hxc]
        refine (hR _ _ (hs1 _) hx).2 ?_
        rw [hs2, QuotientGroup.out_eq']
      · rw [dite_eq_right hT] at hc
        exact absurd rfl hc

  have hRi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (a : GU Dv.σw n) (c : K), H (a * c) = H a :=
    fun H hH a c => by simpa using hH.1 1 c a
  have hLi : ∀ (H : GU Dv.σw n → ℂ), H ∈ Hecke ℂ K → ∀ (c : K) (a : GU Dv.σw n), H (c * a) = H a :=
    fun H hH c a => by simpa using hH.1 c 1 a
  have hconvR : ∀ (a : GU Dv.σw n) (c : K), conv K h h' (a * c) = conv K h h' a := by
    intro a c
    simp only [Formalism.UG.conv]
    refine finsum_congr fun x => ?_
    rw [← mul_assoc, hRi h' hh']
  have hfin : ∀ H ∈ Hecke ℂ K, Set.Finite {d : GU Dv.σw n ⧸ K | H d.out ≠ 0} := by
    rintro H ⟨-, S, hS⟩
    refine (S.finite_toSet.biUnion fun t _ => _root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram t).subset ?_
    intro d hd
    obtain ⟨t, ht, a, b, hab⟩ := hS _ hd
    refine Set.mem_biUnion ht ⟨(a : GU Dv.σw n), a.2, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' d]
    rw [hab]
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  have hfU : ∀ a b : GAf L n, (a : GAf L n ⧸ U) = b → ∀ g, f (g * a) = f (g * b) := by
    intro a b hab g
    have hu := QuotientGroup.eq.1 hab
    have : f (g * a * (a⁻¹ * b)) = f (g * a) := congrFun (hf _ hu) (g * a)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  funext g
  rw [step2 _ hconvR f g, step2 h (hRi h hh) _ g]
  have inner : ∀ d : GU Dv.σw n ⧸ K,
      heckeFunI L n U Dv h' f (g * (heT d).choose) =
        ∑ᶠ e : GU Dv.σw n ⧸ K, h' (d.out⁻¹ * e.out) • f (g * (heT e).choose) := by
    intro d
    rw [step2 h' (hRi h' hh') f]
    set x := lam (heT d).choose with hx
    have hk : x⁻¹ * d.out ∈ K := QuotientGroup.eq.1 (by rw [QuotientGroup.out_eq']; exact hρ2 d)
    have hL : ∀ y, h' (d.out⁻¹ * y) = h' (x⁻¹ * y) := by
      intro y
      have := hLi h' hh' ⟨(x⁻¹ * d.out)⁻¹, inv_mem hk⟩ (x⁻¹ * y)
      rw [← this]
      congr 1
      show _ = (x⁻¹ * d.out)⁻¹ * (x⁻¹ * y)
      group
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (GU Dv.σw n ⧸ K)))
    refine finsum_congr fun e => ?_
    simp only [MulAction.toPerm_apply]
    congr 1
    · rw [hL]
      refine eq_of_coset (hRi h' hh') ?_
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq',
        inv_smul_smul]
    · rw [mul_assoc]
      refine hfU _ _ ((hR _ _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul (hρ1 d) (hρ1 e)) (hρ1 _)).2 ?_) g
      rw [map_mul, hρ2, ← hx, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, hρ2]
  rw [finsum_congr fun d => congrArg (h d.out • ·) (inner d)]
  have hSe : Set.Finite (⋃ (d : GU Dv.σw n ⧸ K) (_ : d ∈ {d : GU Dv.σw n ⧸ K | h d.out ≠ 0}),
      (fun c : GU Dv.σw n ⧸ K => (d.out • c : GU Dv.σw n ⧸ K)) '' {c : GU Dv.σw n ⧸ K | h' c.out ≠ 0}) :=
    (hfin h hh).biUnion fun d _ => (hfin h' hh').image _
  have hmem : ∀ d e : GU Dv.σw n ⧸ K, h d.out ≠ 0 → h' (d.out⁻¹ * e.out) ≠ 0 →
      e ∈ hSe.toFinset := by
    intro d e hd he'
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_biUnion hd ⟨d.out⁻¹ • e, ?_, smul_inv_smul d.out e⟩
    have hc : (((d.out⁻¹ • e).out : GU Dv.σw n) : GU Dv.σw n ⧸ K) = ↑(d.out⁻¹ * e.out) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
    show h' (d.out⁻¹ • e).out ≠ 0
    rw [eq_of_coset (hRi h' hh') hc]
    exact he'
  have hL1 : (∑ᶠ e : GU Dv.σw n ⧸ K, conv K h h' e.out • f (g * (heT e).choose)) =
      ∑ e ∈ hSe.toFinset, (∑ d ∈ (hfin h hh).toFinset, h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_]
    · refine Finset.sum_congr rfl fun e _ => ?_
      congr 1
      show (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out)) = _
      apply finsum_eq_sum_of_support_subset
      intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact left_ne_zero_of_mul hd
    · intro e he
      rw [Function.mem_support] at he
      have h1 : conv K h h' e.out ≠ 0 := fun h0 => he (by rw [h0, zero_smul])
      obtain ⟨d, hd⟩ : ∃ d : GU Dv.σw n ⧸ K, h d.out * h' (d.out⁻¹ * e.out) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h1 (finsum_eq_zero_of_forall_eq_zero hcon)
      exact hmem d e (left_ne_zero_of_mul hd) (right_ne_zero_of_mul hd)
  have hR1 : (∑ᶠ d : GU Dv.σw n ⧸ K, h d.out • ∑ᶠ e : GU Dv.σw n ⧸ K,
      h' (d.out⁻¹ * e.out) • f (g * (heT e).choose)) =
      ∑ d ∈ (hfin h hh).toFinset, ∑ e ∈ hSe.toFinset, (h d.out * h' (d.out⁻¹ * e.out)) •
        f (g * (heT e).choose) := by
    rw [finsum_eq_sum_of_support_subset _ (s := (hfin h hh).toFinset) ?_]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rw [finsum_eq_sum_of_support_subset _ (s := hSe.toFinset) ?_, Finset.smul_sum]
      · exact Finset.sum_congr rfl fun e _ => by rw [mul_smul]
      · intro e he
        rw [Function.mem_support] at he
        exact hmem d e hd (fun h0 => he (by rw [h0, zero_smul]))
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hd (by rw [h0, zero_smul])
  rw [hL1, hR1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_smul]

theorem heckeFunI_conv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ h' ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (conv (KU Dv.σw n) h h') f = heckeFunI L n U Dv h (heckeFunI L n U Dv h' f) := by
  intro L _ _ _ n v w Dv U hU W _ _ h hh h' hh' f hf
  exact conv_of Dv U hU (_root_.GlobalTheory.InertLocUnitary.main L n v w Dv) (_root_.GlobalTheory.InertUmaxInt.loc_integral_of_mem_Umax L n v w Dv) (_root_.GlobalTheory.InertLocSurj.exists_trivOutside_loc_eq L n v w Dv)
    W h hh h' hh' f hf

end GlobalTheory.InertConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSpecHomSpecMapAppTop
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped NumberField
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.FiberCard

theorem isoSpec_hom_specMap_appTop' {P : Scheme.{0}} [IsAffine P] {R : CommRingCat.{0}} (s : P ⟶ Spec R) :
    P.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appTop) = s := by
  rw [Scheme.isoSpec_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end GlobalTheory.IwLevel.FiberCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundSplitPrime
section
namespace GlobalTheory.AtG

theorem jetSplitAmb_holds : JetSplitAmb := by
  intro D X s cc δ B χ cD hok hcc hδ hχ a b S N N' p _ ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m
  exact Formalism.L2.Ker.Test.jetAtSplit_ambOf s B χ cD hok hcc hδ hχ a b S N N' p ι hae hbe hN hN' hsN hsN' hdisc hcD hp hpd hLa π pE hπ hππ hS c' x hc' hpc hx m

end GlobalTheory.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquivStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedParabolicInduction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  first | exact @GlobalTheory.SmGL.Relabel.parInd_reindex | exact GlobalTheory.SmGL.Relabel.parInd_reindex | (intros; apply GlobalTheory.SmGL.Relabel.parInd_reindex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V), IsSmooth π → ∀ (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin t), Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  first | exact @GlobalTheory.ProdReorder.ind₂_unit_left | exact GlobalTheory.ProdReorder.ind₂_unit_left | (intros; apply GlobalTheory.ProdReorder.ind₂_unit_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterBlockSumEqDirectSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potSemistableParameter_blockSum_eq_directSum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a b : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (s' : ↥(Dec (F := E) A) →* GL (Fin b) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L s') → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) = (wdPst P ι Bw h hj (Bw.repE L s)).lpSum (wdPst P ι Bw h hj (Bw.repE L s')) := by
  first | exact @GlobalTheory.Pst.SumOneField.wdPst_sumRep | exact GlobalTheory.Pst.SumOneField.wdPst_sumRep | (intros; apply GlobalTheory.Pst.SumOneField.wdPst_sumRep <;> assumption)
end

