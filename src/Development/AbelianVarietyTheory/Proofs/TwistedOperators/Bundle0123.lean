module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

noncomputable def tprodInnerFun {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (w : ∀ i, E i) : (⨂[ℂ] i, E i) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap (fun i => (innerSL ℂ (w i)).toLinearMap))

theorem tprodInnerFun_tprod {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (w v : ∀ i, E i) :
    tprodInnerFun w (PiTensorProduct.tprod ℂ v) = ∏ i, ⟪w i, v i⟫_ℂ := by
  simp [tprodInnerFun]

theorem eq_zero_of_tprodInnerFun {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (x : ⨂[ℂ] i, E i) (h : ∀ w, tprodInnerFun w x = 0) : x = 0 := by
  classical
  have hx : x ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := E))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  obtain ⟨n, f, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose v hv using fun j => (g j).2
  let W : ∀ i, Submodule ℂ (E i) := fun i => Submodule.span ℂ (Set.range fun j => v j i)
  haveI : ∀ i, FiniteDimensional ℂ (W i) := fun i =>
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let b := fun i => stdOrthonormalBasis ℂ (W i)
  have hexp : ∀ j i, v j i = ∑ k, ⟪(b i k : E i), v j i⟫_ℂ • (b i k : E i) := by
    intro j i
    have hm : v j i ∈ W i := Submodule.subset_span ⟨j, rfl⟩
    have := congrArg (fun z : W i => (z : E i)) ((b i).sum_repr' ⟨v j i, hm⟩)
    simpa using this.symm
  have hj : ∀ j, PiTensorProduct.tprod ℂ (v j) =
      ∑ k : ∀ i, Fin (Module.finrank ℂ (W i)),
        (∏ i, ⟪(b i (k i) : E i), v j i⟫_ℂ) • PiTensorProduct.tprod ℂ (fun i => (b i (k i) : E i)) := by
    intro j
    have e : v j = fun i => ∑ k, ⟪(b i k : E i), v j i⟫_ℂ • (b i k : E i) := funext (hexp j)
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp only [RingHom.id_apply]
  have hx' : x = ∑ j, f j • PiTensorProduct.tprod ℂ (v j) := by
    rw [← hg]; simp [hv]
  have key : x = ∑ k : ∀ i, Fin (Module.finrank ℂ (W i)),
      tprodInnerFun (fun i => (b i (k i) : E i)) x • PiTensorProduct.tprod ℂ (fun i => (b i (k i) : E i)) := by
    conv_rhs => rw [hx']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, tprodInnerFun_tprod, Finset.sum_smul]
    rw [Finset.sum_comm, hx']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hj j, Finset.smul_sum]
    simp [smul_smul]
  rw [key]; simp [h]

theorem eq_zero_of_integral_fundDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hc : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) (hi : IntegrableOn (fun g => star (F g) * F g) 𝓕 μ)
    (h0 : ∫ g in 𝓕, star (F g) * F g ∂μ = 0) : F = 0 := by
  have e : ∀ g, star (F g) * F g = ((‖F g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.conj_mul']; simp
  simp only [e] at hi h0
  rw [integral_complex_ofReal] at h0
  have h0' : ∫ g in 𝓕, ‖F g‖ ^ 2 ∂μ = 0 := by exact_mod_cast h0
  have hi' : Integrable (fun g => ‖F g‖ ^ 2) (μ.restrict 𝓕) := by
    have := Integrable.re hi
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 h0'
  have hae' : ∀ᵐ g ∂μ.restrict 𝓕, F g = 0 := hae.mono fun g hg => by simpa using hg
  have ho : IsOpen {g | F g ≠ 0} := isOpen_ne_fun hc continuous_const
  have hz : μ {g | F g ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun γ => ?_) ?_
    · ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [Set.mem_setOf_eq]
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ (γ⁻¹).2]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact hae'
  have := (ho.measure_eq_zero_iff μ).1 hz
  funext g
  by_contra hg
  have : g ∈ {g | F g ≠ 0} := hg
  simp_all

theorem multT_eq_zero_of_apply_eq_zero : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → ∀ u ∈ MultT θ M J χ, ∀ x : ⨂[ℂ] τ, M.sm τ, x ≠ 0 → u x = 0 → u = 0 := by
  intro D V S θ M J χ μ 𝓕 hθ hμ h𝓕 hS u hu x hx hux
  obtain ⟨-, -, -, hB, hG, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  rw [mem_multT] at hu
  set T : MMap M := PiTensorProduct.lift.symm u with hT
  have hTv : ∀ v, T v = u (PiTensorProduct.tprod ℂ v) := fun v => by simp [hT]
  obtain ⟨c, hc⟩ := hS hθ hμ h𝓕 T hu T hu
  have hall : ∀ (w : M.Vec) (y : ⨂[ℂ] τ, M.sm τ), IntegrableOn (fun g => star (T w g) * u y g) 𝓕 μ ∧
      ∫ g in 𝓕, star (T w g) * u y g ∂μ = c * tprodInnerFun w y := by
    intro w y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      obtain ⟨h1, h2⟩ := hc w v
      have e : (fun g => star (T w g) * u (r • PiTensorProduct.tprod ℂ v) g) =
          fun g => r * (star (T w g) * T v g) := by
        funext g; rw [map_smul, ← hTv]; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine ⟨h1.const_mul r, ?_⟩
      rw [integral_const_mul, h2, map_smul, tprodInnerFun_tprod]
      simp only [Submodule.coe_inner, smul_eq_mul]; ring
    | add y z hy hz =>
      have e : (fun g => star (T w g) * u (y + z) g) =
          fun g => star (T w g) * u y g + star (T w g) * u z g := by
        funext g; rw [map_add (f := _)]; simp only [Pi.add_apply]; ring
      rw [e]
      refine ⟨hy.1.add hz.1, ?_⟩
      rw [integral_add hy.1 hz.1, hy.2, hz.2, map_add (f := _)]; ring
  have hc0 : c = 0 := by
    by_contra hne
    refine hx (eq_zero_of_tprodInnerFun x fun w => ?_)
    have := (hall w x).2
    rw [hux] at this
    simp only [Pi.zero_apply, mul_zero, integral_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hne
  have hT0 : ∀ v, T v = 0 := by
    intro v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.mult_value_left_cont_level θ M J χ T hu v
    refine eq_zero_of_integral_fundDomain (GQ V) μ 𝓕 h𝓕 (T v) h2 h1 (hc v v).1 ?_
    rw [(hc v v).2, hc0, zero_mul]
  refine PiTensorProduct.ext ?_
  ext v g
  simp [← hTv, hT0]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealFockAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.Proof.RealFockActionTwistedOperators

theorem thetaKO_rat_mul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (h : GA D S) (g : GA D T) :
    thetaKO om (γ * h) g f = thetaKO om h g f := by
  unfold thetaKO
  have hp : ((γ * h, g) : GA D S × GA D T) = (γ, 1) * (h, g) := by simp
  rw [hp, map_mul, mul_apply_eq_comp]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)

theorem thetaKO_mul_right {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (f : WO S T → ℂ) (h u : GA D S) (g : GA D T) :
    thetaKO om (h * u) g f = thetaKO om h g (om (u, 1) f) := by
  unfold thetaKO
  have hp : ((h * u, g) : GA D S × GA D T) = (h, g) * (u, 1) := by simp
  rw [hp, map_mul, mul_apply_eq_comp]

theorem adForms_rat {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {f : G → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    (γ : Γ) (h : G) : f (ι γ * h) = ρ γ (f h) := by
  have h1 : f (ι γ * h * ((1 : J) : G)) = (χ 1 : ℂ) • ρ γ (f h) := hf γ h 1
  simpa using h1

theorem form_rat {D : D7} {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) {γ : GA D V} (hγ : γ ∈ GQ V)
    (h : GA D V) : c.ext f (γ * h) = c.ρ (γ * h)⁻¹ (c.ρ γ (f ((finHom V).rangeRestrict h))) := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = _
  congr 1
  have hr : (finHom V).rangeRestrict (γ * h) = Bridge.ratF V ⟨γ, hγ⟩ * (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [Bridge.ratF]
  rw [hr, adForms_rat (Bridge.ratF V) hf ⟨γ, hγ⟩]
  rfl

theorem ext_mul_real {D : D7} {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) {u : GA D V} (hu : u ∈ GinfC V)
    (h : GA D V) : c.ext f (h * u) = c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict h)) := by
  have hu' : finHom V u = 1 := hu
  have hr : (finHom V).rangeRestrict (h * u) = (finHom V).rangeRestrict h := by
    apply Subtype.ext
    simp [hu']
  show c.ρ (h * u)⁻¹ (f ((finHom V).rangeRestrict (h * u))) = _
  rw [hr]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)

end GlobalTheory.Proof.RealFockActionTwistedOperators

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def TameOn (χ : (AE D)ˣ →* Circle) (e : AE D) (P : Finset (Pl D.host.E))
    (c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
    toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → cA D e * (x : AE D) = cA D e →
    ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩) →
      ((χ x : Circle) : ℂ) = ∏ PP ∈ P, ((c PP (u PP) : ℂˣ) : ℂ)

def vacScal {S T : HSp D} (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E))
    (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (g : GA D S) (h : GA D T) : ℂ :=
  ∏ PP ∈ P, (((cT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ)⁻¹ *
    ((cS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ))


open Classical in
def resChr {T0 : Type} (L : LevCh D T0) (t : T0) (n : ℕ) (PP : Pl D.host.E) : (kP PP)ˣ →* ℂˣ :=
  if PP ∈ L.Pg then (L.chi n PP)⁻¹ else L.xiR t PP

end GlobalTheory.StepLaw

end
end

