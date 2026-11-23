module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameLocalCharacterDetCongruentOneEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.TwV.AwayCpl.RhoOne

open GlobalTheory.TopStep

theorem redGL_eq_one_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (D : ℕ) (hD : 1 ≤ D) (k : GLint E n P)
    (hk : ∀ s l, IntAt P ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l))) :
    redGL n P k = 1 := by
  apply Units.ext
  rw [redGL_val, Units.val_one]
  ext a b
  have hq := qOf_ne_zero (P := P)
  have hint : IntAt P ((k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E)) := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    have e : (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E) =
        ((qOf P : ℕ) : E) ^ d * ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a)) := by
      rw [hd, pow_succ]
      field_simp
    rw [e]
    exact (intAt_pow (intAt_nat _) _).mul (hk b a)
  have h0 := redP_eq_zero_of_div hint
  have hs : IntAt P ((Pi.single b 1 : Sp E n) a) := mem_stdAt.1 (single_mem_stdAt b) a
  rw [reduction_sub (glint_entry k a b) hs, sub_eq_zero] at h0
  rw [redMat, Matrix.of_apply, h0]
  by_cases h : a = b
  · subst h
    simp [reduction_one₂]
  · simp [Pi.single_apply, h, reduction_zero]

theorem rhoS_det_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
  intro X Pr R Ch sel S mu cst hc i n P k hk
  have hred := redGL_eq_one_of_cong (cst.D P) (hc.D_pos P) k hk
  have hdet : redP P.1 ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
    rw [(det_glint k).2, ← redGL_val, hred, Units.val_one, Matrix.det_one]
  unfold rhoS LocE.unitV
  rw [hdet]
  simp

end GlobalTheory.TwV.AwayCpl.RhoOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalization
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrameLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by funext l; simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

theorem seamVec_apply {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (x : Sp X.E n) (l : Fin n) :
    seamVec s n x l = s.iE (x l) := rfl

theorem seamVec_injective {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : Function.Injective (seamVec s n) := by
  intro x y hxy
  funext l
  exact s.iE.injective (congrFun hxy l)

theorem seam_lat_eq_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat M = M.map (seamVec s n) := by
  unfold Seam.lat
  rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (M : Set (Sp X.E n))) = seamVec s n '' M from rfl,
    ← Submodule.map_coe]
  exact Submodule.span_eq _

theorem localization_map_seamVec {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E))
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (M.map (seamVec s n)) = (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M).map (seamVec s n) := by
  set ψ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE with hψ
  ext x
  constructor
  · rintro ⟨r, hr, z, hz, hzx⟩
    have hfy : seamVec s n (fun l => s.iE.symm (x l)) = x := by
      funext l
      simp [seamVec_apply]
    refine ⟨fun l => s.iE.symm (x l), ⟨ψ.symm r, ?_, ?_⟩, hfy⟩
    · intro hm
      apply hr
      have := (mem_seamP s P (ψ.symm r)).2 hm
      simpa [ψ] using this
    · have : ψ.symm r • (fun l => s.iE.symm (x l)) = z := by
        apply seamVec_injective s n
        rw [(seamVec s n).map_smulₛₗ, hfy, hzx]
        show ψ (ψ.symm r) • x = r • x
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact hz
  · rintro ⟨y, ⟨r, hr, hy⟩, rfl⟩
    refine ⟨ψ r, ?_, r • y, hy, ?_⟩
    · intro hm
      exact hr ((mem_seamP s P r).1 hm)
    · rw [(seamVec s n).map_smulₛₗ]
      rfl

theorem stdLat_map_seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    (stdLat X.E n).map (seamVec s n) = stdLat D.host.E n := by
  ext y
  rw [Submodule.mem_map]
  unfold Formalism.L2.Col.stdLat
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hx l)
    refine (Submodule.mem_one).2 ⟨RingOfIntegers.mapRingEquiv s.iE r, ?_⟩
    rw [seamVec_apply, ← hr]
    rfl
  · intro hy
    refine ⟨fun l => s.iE.symm (y l), fun l => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hy l)
      refine (Submodule.mem_one).2 ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, ?_⟩
      show _ = s.iE.symm (y l)
      rw [← hr]
      rfl
    · funext l
      simp [seamVec_apply]

theorem mvL_seamGL_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    mvL (seamGL s g) (M.map (seamVec s n)) = (M.map (g.toLinearMap.restrictScalars (𝓞 X.E))).map (seamVec s n) := by
  unfold mvL
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
    show seamVec s n (g x) = toLE (seamGL s g) (seamVec s n x)
    rw [toLE_apply]
    exact (seamGL_mulVec s g x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨seamVec s n x, ⟨x, hx, rfl⟩, ?_⟩
    show toLE (seamGL s g) (seamVec s n x) = seamVec s n (g x)
    rw [toLE_apply]
    exact seamGL_mulVec s g x

theorem seamGL_stdAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) →
    mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  intro D X s n P g N hg
  have hstd : (stdAt X.E n P).map (g.toLinearMap.restrictScalars (𝓞 X.E)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg x).2 hx
    · intro hy
      refine ⟨g.symm y, (hg _).1 (by simpa using hy), by simp⟩
  show mvL (seamGL s g) (Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (stdLat D.host.E n)) = _
  rw [← stdLat_map_seamVec s n, localization_map_seamVec, mvL_seamGL_map, ← stdAt, hstd, seam_lat_eq_map, localization_map_seamVec]

end GlobalTheory.FrameLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.FormsStd

section Gen

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}

theorem cSpan_eq_VV (lam : ι → DomWeight n) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, nablaSq_eq_delSq]
  rfl

theorem mem_ValC_iff_isVal (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ GlobalTheory.KerJ.IsVal (fun y : Fr emb σ n => y.1) lam (RingHom.id ℂ) f := by
  have key : ∀ P : Pol ℂ ι n, fnOf (Gr emb σ n) (shiftOf lam) 1 P = evG (fun y : Fr emb σ n => y.1) (fun τ => (lam τ).detShift)
      (RingHom.id ℂ) P := by
    intro P
    funext y
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, evG, shiftOf]
    rfl
  unfold ValC GlobalTheory.KerJ.IsVal
  rw [Submodule.mem_map, cSpan_eq_VV]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, key P⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, hP, key P⟩

theorem tr_eq_iff (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (b : S.β) (g : S.G b) (f : Fr emb σ n → ℂ) :
    S.tr emb σ b g f = f ↔ ∀ y y' : Fr emb σ n,
      (∀ τ, y.1 τ = ((S.gam b g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y'.1 τ) →
        f y = σ ((S.chr b g : Kˣ) : K) * f y' := by
  constructor
  · intro h y y' hy
    have hy' : y = frMul emb σ (S.gam b g) y' := Subtype.ext (funext hy)
    have e := congrFun h y
    rw [GStep.tr, trFr_apply, hy', ← GlobalTheory.Mem.Col2.frMul_mul, inv_mul_cancel, GlobalTheory.Mem.Col2.frMul_one] at e
    rw [hy']
    exact e.symm
  · intro h
    funext y
    rw [GStep.tr, trFr_apply]
    refine (h y (frMul emb σ (S.gam b g)⁻¹ y) fun τ => ?_).symm
    show y.1 τ = _ * ((((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * y.1 τ)
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end Gen

theorem embT_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) :
    TaylorLogMetric.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
  funext τ
  ext y
  show B.host.φ₀ _ = _
  rw [← B.embE_φ₀]
  rfl

theorem lamTG_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word)
    (a : I.ι) (i : ℕ) : lamTG ((I.tw l l0 Z).fm u a) i = lamT (B.hcW u) i := by
  funext τ
  obtain ⟨c, hc⟩ := B.R.t_odd
  have h : (((i * ((I.rec7 l Z).R.t + 1) / 2 : ℕ) : ℤ)) = (i : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    show (((i * (B.R.t + 1) / 2 : ℕ) : ℤ)) = _
    rw [hc, show 2 * c + 1 + 1 = 2 * (c + 1) by ring, mul_left_comm, Nat.mul_div_cancel_left _ two_pos,
      Nat.mul_div_cancel_left _ two_pos]
    push_cast
    ring
  show Formalism.L2.Forms.shW _ _ = GlobalTheory.Mem.Col2.shW _ _
  unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
  congr 1
  funext r
  have hx : (((I.tw l l0 Z).fm u a).lam i τ).w r = (Examples₂.lamOf (B.hcW u τ) i).w r := rfl
  rw [hx, h]
  ring

theorem formsAre_stabStd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Qp : I.ι → Finset ℕ) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ∀ u a, GlobalTheory.KerJ.FormsAre ((I.tw l l0 Z).fm u a) (O u a) (GlobalTheory.Pdv.stabStd I l Z u a) := by
  intro B X I _hOk _hP l Z l0 Qp O hO u a
  have hfr : ∀ i, (O u a).frm i = fun y => y.1 := fun i => funext (hO.frm u a i)
  have hemb := embT_eq I l Z
  have hlaw : ∀ i (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
      (I.stp u a i).tr B.fields.emb B.embLL c.1 s.1 f = f ↔
        GlobalTheory.KerJ.LawAt (O u a) i ((((I.stp u a i).gam c.1 s.1 : GL (Fin (B.R.N i)) B.host.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E),
          B.embLL (((I.stp u a i).chr c.1 s.1 : B.LLˣ) : B.LL)) f := by
    intro i c s f
    rw [tr_eq_iff]
    unfold GlobalTheory.KerJ.LawAt
    simp only [hfr i, hemb]
    exact Iff.rfl
  refine ⟨?_, ?_⟩
  · intro i _ φ hφ c
    have hφ' : ∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧
        ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c := hφ
    rw [hfr i, lamTG_eq I l Z l0 u a i]
    exact (mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ' c).1
  · intro i _ _ φ
    rw [hfr i, lamTG_eq I l Z l0 u a i]
    show (∀ c, φ c ∈ ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i) ∧
        ∀ g : (I.stp u a i).Stab c, (I.stp u a i).tr B.fields.emb B.embLL c.1 g.1 (φ c) = φ c) ↔ _
    constructor
    · intro hφ c
      refine ⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).1 (hφ c).1, ?_⟩
      rintro g ⟨s, rfl⟩
      exact (hlaw i c s (φ c)).1 ((hφ c).2 s)
    · intro hφ c
      refine ⟨(mem_ValC_iff_isVal B.fields.emb B.embLL _ (φ c)).2 (hφ c).1, fun s => ?_⟩
      exact (hlaw i c s (φ c)).2 ((hφ c).2 _ ⟨s, rfl⟩)

end GlobalTheory.Pdv.FormsStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixingStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  first | (exact @GlobalTheory.RoadU.unram_comp_normU_of_fix) | (exact GlobalTheory.RoadU.unram_comp_normU_of_fix) | (intros; apply GlobalTheory.RoadU.unram_comp_normU_of_fix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
section
noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV _root_.Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def topF {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

theorem xiTop_eq_prod {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x * ∏ P, topF Ch sel mu cst i P p Y p' x := rfl

end GlobalTheory.TwTop

end
end

