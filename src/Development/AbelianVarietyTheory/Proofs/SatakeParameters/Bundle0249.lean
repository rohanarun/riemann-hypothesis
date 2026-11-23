module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntUOfOneOffOrdA
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

open Formalism.UG.P

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneExc (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  afsplitI w a + (1 - afsplitI w 1)

theorem oneExc_self (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) : oneExc w a w = a := by
  rw [oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_self, afsplitI_self, afsplit_one_apply, sub_self, add_zero]

theorem oneExc_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : w.adicCompletion F) : oneExc w a w' = 1 := by
  rw [oneExc, afsplit_add_apply, afsplit_sub_apply, afsplitI_ne w w' h, afsplitI_ne w w' h, afsplit_one_apply, sub_zero,
    zero_add]

theorem oneExc_mem (w : HeightOneSpectrum (𝓞 F)) (a : w.adicCompletion F) (ha : a ∈ w.adicCompletionIntegers F) :
    oneExc w a ∈ intAd F := by
  intro w'
  by_cases h : w' = w
  · subst h; rw [oneExc_self]; exact ha
  · rw [oneExc_ne w w' h]; exact one_mem _

theorem mem_RInt_of_quad (z : AfE F E) (w : HeightOneSpectrum (𝓞 F)) (a b : w.adicCompletion F)
    (ha : a ∈ w.adicCompletionIntegers F) (hb : b ∈ w.adicCompletionIntegers F)
    (hoff : ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → prV (E := E) w' z = 1)
    (hv : (prV (E := E) w z - (1 : E) ⊗ₜ[F] a) * (prV (E := E) w z - (1 : E) ⊗ₜ[F] b) = 0) :
    z ∈ RInt F E := by
  obtain ⟨ι, hι⟩ := GlobalTheory.TwU.exists_isAdIso F E
  have hca : ((1 : E) ⊗ₜ[F] oneExc w a : AfE F E) ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w a ha⟩, rfl⟩)
  have hcb : ((1 : E) ⊗ₜ[F] oneExc w b : AfE F E) ∈ RInt F E :=
    Subring.subset_closure (Or.inr ⟨⟨_, oneExc_mem w b hb⟩, rfl⟩)
  have hq : (z - (1 : E) ⊗ₜ[F] oneExc w a) * (z - (1 : E) ⊗ₜ[F] oneExc w b) = 0 := by
    refine afsplit_inj _ fun w' => ?_
    rw [map_mul, map_sub, map_sub, afsplit_prV_tmul, afsplit_prV_tmul]
    by_cases h : w' = w
    · subst h
      rw [oneExc_self, oneExc_self]
      exact hv
    · rw [oneExc_ne w w' h, oneExc_ne w w' h, hoff w' h, ← Algebra.TensorProduct.one_def, sub_self, zero_mul]
  rw [hι.2]
  intro P
  have h1 := congrArg (fun x => ι x P) hq
  simp only [map_mul, map_sub, map_zero] at h1
  have h2 : (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w a) P) * (ι z P - ι ((1 : E) ⊗ₜ[F] oneExc w b) P) = 0 := h1
  rcases mul_eq_zero.1 h2 with h | h
  · rw [sub_eq_zero.1 h]; exact (hι.2 _).1 hca P
  · rw [sub_eq_zero.1 h]; exact (hι.2 _).1 hcb P

end SlopeTestRemainingChoices

section Main

theorem mem_intU_of_oneOff_ordA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → LocInt A →
    SplAlg A → ∀ v, ∀ y ∈ U1 σ, OneOff (A.pl v).1 y → ordA A v y = 0 → y ∈ intU F E := by
  intro F E _ _ _ _ _ σ n p G A J _ hG hI hS v y hy hoff hord
  set w := (A.pl v).1 with hw
  set s := A.spl v (prV (E := E) w (y : AfE F E)) with hs_def
  have hy1 : (y : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (y : AfE F E) = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hy)
    exact h
  have hprod : prV (E := E) w (y : AfE F E) * sigR σ (w.adicCompletion F) (prV (E := E) w (y : AfE F E)) = 1 := by
    have h := congrArg (prV (E := E) w) hy1
    rw [map_mul, map_one] at h
    rw [← h]
    congr 1
    exact (DFunLike.congr_fun (afsplit_prV_comp_sigR σ w) _).symm
  have hss : s.1 * s.2 = 1 := by
    have h := congrArg (A.spl v) hprod
    rw [map_mul, hG.sig v, map_one] at h
    exact congrArg Prod.fst h
  have hss' : s.2 * s.1 = 1 := by rw [mul_comm]; exact hss
  have hset := G.P.setting v
  haveI := hset.frac_alt
  have hp := hset.p_unif
  set x : G.P.Qq v := (A.eQ v).symm s.1 with hx_def
  have hxe : A.eQ v x = s.1 := RingEquiv.apply_symm_apply _ _
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hxe
    rw [← hxe, zero_mul] at hss
    exact zero_ne_one hss
  obtain ⟨k, u, hu⟩ := exists_eq_unit_mul_zpow₂ hp hx0
  have hk : k = 0 := by
    have h1 : ordA A v y = ordP (G.P.W v) p x := rfl
    rw [h1, hu, ordP_eq hp] at hord
    exact hord
  subst hk
  rw [zpow_zero, mul_one] at hu
  have ha : s.1 ∈ w.adicCompletionIntegers F := by
    rw [← hxe]
    exact (hI v x).1 ⟨u, hu.symm⟩
  have hb : s.2 ∈ w.adicCompletionIntegers F := by
    have h2 : s.2 = A.eQ v x⁻¹ := by
      rw [map_inv₀, hxe]
      exact eq_inv_of_mul_eq_one_right hss
    rw [h2]
    refine (hI v x⁻¹).1 ⟨(u⁻¹ : (G.P.W v)ˣ), ?_⟩
    rw [hu]
    exact map_units_inv (algebraMap (G.P.W v) (G.P.Qq v) : G.P.W v →* G.P.Qq v) u
  have key : ∀ t : E ⊗[F] w.adicCompletion F, ((A.spl v t).1 - s.1) * ((A.spl v t).1 - s.2) = 0 →
      ((A.spl v t).2 - s.1) * ((A.spl v t).2 - s.2) = 0 →
      (t - (1 : E) ⊗ₜ[F] s.1) * (t - (1 : E) ⊗ₜ[F] s.2) = 0 := by
    intro t h1 h2
    apply (A.spl v).injective
    rw [map_mul, map_sub, map_sub, hS v, hS v, map_zero]
    exact Prod.ext h1 h2
  have hyR : (y : AfE F E) ∈ RInt F E := by
    refine mem_RInt_of_quad _ w s.1 s.2 ha hb hoff (key _ ?_ ?_)
    · show (s.1 - s.1) * (s.1 - s.2) = 0
      rw [sub_self, zero_mul]
    · show (s.2 - s.1) * (s.2 - s.2) = 0
      rw [sub_self, mul_zero]
  have hinv : ∀ w' : HeightOneSpectrum (𝓞 F),
      prV (E := E) w' ((y⁻¹ : (AfE F E)ˣ) : AfE F E) * prV (E := E) w' (y : AfE F E) = 1 := by
    intro w'
    rw [← map_mul, Units.inv_mul, map_one]
  set t := A.spl v (prV (E := E) w ((y⁻¹ : (AfE F E)ˣ) : AfE F E)) with ht_def
  have hts : t * s = 1 := by rw [ht_def, hs_def, ← map_mul, hinv w, map_one]
  have ht1 : t.1 = s.2 := by
    have h : t.1 * s.1 = 1 := congrArg Prod.fst hts
    calc t.1 = t.1 * (s.1 * s.2) := by rw [hss, mul_one]
      _ = (t.1 * s.1) * s.2 := (mul_assoc _ _ _).symm
      _ = s.2 := by rw [h, one_mul]
  have ht2 : t.2 = s.1 := by
    have h : t.2 * s.2 = 1 := congrArg Prod.snd hts
    calc t.2 = t.2 * (s.2 * s.1) := by rw [hss', mul_one]
      _ = (t.2 * s.2) * s.1 := (mul_assoc _ _ _).symm
      _ = s.1 := by rw [h, one_mul]
  have hyR' : ((y⁻¹ : (AfE F E)ˣ) : AfE F E) ∈ RInt F E := by
    refine mem_RInt_of_quad _ w s.1 s.2 ha hb (fun w' h => ?_) (key _ ?_ ?_)
    · have h3 := hinv w'
      rwa [hoff w' h, mul_one] at h3
    · show (t.1 - s.1) * (t.1 - s.2) = 0
      rw [ht1, sub_self, mul_zero]
    · show (t.2 - s.1) * (t.2 - s.2) = 0
      rw [ht2, sub_self, zero_mul]
  exact (Submonoid.mem_units_iff _ _).2 ⟨hyR, hyR'⟩

end Main

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.CongOne

open GlobalTheory.TopStep GlobalTheory.BlockDecompositionK1

theorem mem_glint_prinCong_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
    {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n) (hD : 1 ≤ D)
    (h : ∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) :
    ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  classical
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hqD : ((qOf P : E) ^ D) ≠ 0 := pow_ne_zero _ hq
  have hsingle : ∀ s l, IntAt P ((Pi.single s (1 : E) : Sp E n) l) := fun s l =>
    mem_stdAt.1 (single_mem_stdAt (P := P) s) l
  have hent : ∀ l s, IntAt P (k (Pi.single s (1 : E)) l) := fun l s => by
    have e : k (Pi.single s (1 : E)) l = (qOf P : E) ^ D * (((qOf P : E) ^ D)⁻¹ *
        (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) + (Pi.single s (1 : E) : Sp E n) l := by
      field_simp
      ring
    rw [e]
    exact ((intAt_pow (intAt_nat (qOf P)) D).mul (h s l)).add (hsingle s l)
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun l s => k (Pi.single s (1 : E)) l
  have hA : ∀ l s, IntAt P (A l s) := hent
  have hAx : ∀ x, A.mulVec x = k x := fun x => by
    funext l
    refine Eq.trans ?_ (apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l).symm
    show ∑ s, A l s * x s = _
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm]
    rfl
  have hred : A.map (redP P) = 1 := by
    ext l s
    rw [Matrix.map_apply]
    have h0 : redP P (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l) = 0 := by
      obtain ⟨c, rfl⟩ : ∃ c, D = c + 1 := ⟨D - 1, by omega⟩
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (h s l)
    rw [reduction_sub (hent l s) (hsingle s l), sub_eq_zero] at h0
    show redP P (k (Pi.single s (1 : E)) l) = _
    rw [h0, Matrix.one_apply, Pi.single_apply]
    split_ifs
    · exact reduction_one₂
    · exact reduction_zero
  have hdet : IsUnit (redP P A.det) := by
    rw [(det_int hA).2, hred, Matrix.det_one]
    exact isUnit_one
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hA hdet
  have hjk : j.1 = k := LinearEquiv.ext fun x => (hj x).trans (hAx x)
  have hk : k ∈ GLint E n P := hjk ▸ j.2
  refine ⟨hk, fun x hx => ?_⟩
  refine mem_stdAt.2 fun l => ?_
  have e1 := apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l
  have e2 := apply_eq_sum (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l
  have e : (((qOf P : E) ^ D)⁻¹ • (k x - x)) l = ∑ s, x s * (((qOf P : E) ^ D)⁻¹ *
      (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) := by
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change ((qOf P : E) ^ D)⁻¹ * ((k : Sp E n →ₗ[E] Sp E n) x l - (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l) = _
    rw [e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [LinearMap.id_apply, LinearEquiv.coe_coe]
    ring
  rw [e]
  exact intAt_sum _ fun s _ => (mem_stdAt.1 hx s).mul (h s l)

end GlobalTheory.CongOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Apx

variable {D : D7} {X : Fields} (s : Seam D X)

def apxAt {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (k : GL (Fin N) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Sp X.E N ≃ₗ[X.E] Sp X.E N :=
  Classical.epsilon fun g : Sp X.E N ≃ₗ[X.E] Sp X.E N => NearAt (seamP s P) n k (seamGL s g)

def seamVec (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by
    funext l
    simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

def latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 X.E) (Sp X.E n) :=
  L.comap (seamVec s n)

theorem mem_latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Sp X.E n) :
    y ∈ latBack s L ↔ (fun l => s.iE (y l)) ∈ L := Iff.rfl

end Apx

section Ad

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def latAdX (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  latBack t.seam (latCo D.sp (gramN D i hi) (A.crd i hi) a x ((St i hi).K β).lev.Lb)




end Ad

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfCongOneModQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.ParahoricOfCong

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem mem_stdAt_iff_sclLat_zero (q N : ℕ) (x : Sp E N) :
    x ∈ stdAt E N P ↔ x ∈ LocE.sclLat P q N (fun _ => 0) := by
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
  simp

theorem map_mem_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (h : Sp E N ≃ₗ[E] Sp E N) (hh : ∀ x ∈ stdAt E N P, q⁻¹ • (h x - x) ∈ stdAt E N P) :
    ∀ x ∈ M, h x ∈ M := by
  intro x hx
  have e : h x = x + (h x - x) := by abel
  rw [e]
  exact M.add_mem hx (hqM _ (hh x (hM hx)))

theorem mem_stabL_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (g : Sp E N ≃ₗ[E] Sp E N) (h1 : ∀ x ∈ stdAt E N P, q⁻¹ • (g x - x) ∈ stdAt E N P)
    (h2 : ∀ x ∈ stdAt E N P, q⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) :
    g ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    have := map_mem_of_cong P q M hM hqM g⁻¹ h2 (g x) hx
    have e : g⁻¹ (g x) = x := LinearEquiv.symm_apply_apply g x
    rwa [e] at this
  · exact map_mem_of_cong P q M hM hqM g h1 x

end GlobalTheory.ParahoricOfCong


open GlobalTheory.ParahoricOfCong in
theorem GlobalTheory.ParahoricOfCong.mem_JQ_of_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (kj n c : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)), (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E (n + c) P) → (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E (n + c) P) → g ∈ LocE.JQ P (qOf P) kj n c := by
  intro E _ _ _ P kj n c g h1 h2
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  refine ⟨?_, ?_⟩
  · refine mem_stabL_of_cong P _ _ le_rfl (fun y hy => ?_) g h1 h2
    have e : y = (qOf P : E) • ((qOf P : E)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
    rw [e, Nat.cast_smul_eq_nsmul E]
    exact nsmul_mem hy _
  · refine mem_stabL_of_cong P _ _ ?_ ?_ g h1 h2
    · intro x hx
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)]
      have := GlobalTheory.CongLevel.sclLat_le P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n)
      exact this (by simpa [LocE.parL] using hx)
    · intro y hy
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)] at hy
      have := GlobalTheory.CongLevel.smul_mem_sclLat P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n) y hy
      simpa [LocE.parL] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiAMemRange
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.OrdA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

theorem phiA_mem_range (A : LocAt F E n G) (hI : LocInt A) (hS : SplAlg A) (v : Fin G.P.nV)
    {x : AfE F E} (hx : x ∈ RInt F E) : phiA A v x ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range := by
  haveI := (G.P.setting v).frac_alt
  have key : RInt F E ≤ (algebraMap (G.P.W v) (G.P.Qq v)).range.comap (phiA A v) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      show phiA A v ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range
      rw [phiA_incl]
      have hint : IsIntegral ℤ (A.iw v (algebraMap (𝓞 E) E a)) :=
        (RingOfIntegers.isIntegral_coe a).map (A.iw v).toIntAlgHom
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hint.tower_top (A := G.P.W v))
      exact ⟨y, hy⟩
    · show phiA A v ((1 : E) ⊗ₜ[F] c) ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range
      have h1 : phiA A v ((1 : E) ⊗ₜ[F] c) = (A.eQ v).symm (c (A.pl v).1) := by
        have h2 : prV (E := E) (A.pl v).1 ((1 : E) ⊗ₜ[F] c) = (1 : E) ⊗ₜ[F] c (A.pl v).1 := rfl
        have h3 : A.ph v ((1 : E) ⊗ₜ[F] c (A.pl v).1) = c (A.pl v).1 := by
          show (A.spl v ((1 : E) ⊗ₜ[F] c (A.pl v).1)).1 = _
          rw [hS v]
        show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 ((1 : E) ⊗ₜ[F] c))) = _
        rw [h2, h3]
      rw [h1]
      exact (hI v _).2 (by rw [RingEquiv.apply_symm_apply]; exact hc (A.pl v).1)
  exact key hx

theorem phiA_intU (A : LocAt F E n G) (hI : LocInt A) (hS : SplAlg A) (v : Fin G.P.nV) {k : (AfE F E)ˣ}
    (hk : k ∈ intU F E) : ∃ u : (G.P.W v)ˣ, phiA A v (k : AfE F E) = algebraMap (G.P.W v) (G.P.Qq v) u := by
  haveI := (G.P.setting v).frac_alt
  obtain ⟨a, ha⟩ := phiA_mem_range A hI hS v (x := (k : AfE F E)) hk.1
  obtain ⟨b, hb⟩ := phiA_mem_range A hI hS v (x := ((k⁻¹ : (AfE F E)ˣ) : AfE F E)) hk.2
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (G.P.W v) (G.P.Qq v)
    rw [map_mul, ha, hb, ← map_mul, Units.mul_inv, map_one, map_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha.symm⟩

theorem ordA_mul (A : LocAt F E n G) (v : Fin G.P.nV) (x y : (AfE F E)ˣ) :
    ordA A v (x * y) = ordA A v x + ordA A v y := by
  haveI := (G.P.setting v).frac_alt
  have hp := (G.P.setting v).p_unif
  obtain ⟨a, u, ha⟩ := exists_eq_unit_mul_zpow₂ hp (x.isUnit.map (phiA A v)).ne_zero
  obtain ⟨b, u', hb⟩ := exists_eq_unit_mul_zpow₂ hp (y.isUnit.map (phiA A v)).ne_zero
  unfold ordA
  rw [Units.val_mul, map_mul, ha, hb, ordP_eq hp, ordP_eq hp, ← ordP_eq (Qq := G.P.Qq v) hp (a + b) (u * u')]
  congr 1
  rw [zpow_add₀ (pQ_ne hp), Units.val_mul, map_mul]; ring

theorem ordP_unit (v : Fin G.P.nV) (u : (G.P.W v)ˣ) :
    ordP (G.P.W v) p (algebraMap (G.P.W v) (G.P.Qq v) u) = 0 := by
  haveI := (G.P.setting v).frac_alt
  have := ordP_eq (Qq := G.P.Qq v) (G.P.setting v).p_unif 0 u
  simpa using this

theorem ordA_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ) [Fact p.Prime]
    (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, (∀ x y, ordA A v (x * y) = ordA A v x + ordA A v y) ∧
    (∀ k ∈ intU F E, ordA A v k = 0) ∧ (∀ z : Eˣ, ordA A v (ratId F E z) = ordP (G.P.W v) p (A.iw v (z : E))) ∧
    ∀ v', v' ≠ v → ∀ x, OneOff (A.pl v').1 x → ordA A v x = 0 := by
  intro F E _ _ _ _ _ n p _ G A hI hS v
  refine ⟨ordA_mul A v, fun k hk => ?_, fun z => ?_, fun v' hv x hx => ?_⟩
  · obtain ⟨u, hu⟩ := phiA_intU A hI hS v hk
    unfold ordA
    rw [hu]
    exact ordP_unit v u
  · unfold ordA
    rw [← phiA_incl A v (z : E)]
    rfl
  · have hne : (A.pl v).1 ≠ (A.pl v').1 := fun h => hv (A.pl.injective (Subtype.ext h)).symm
    have h1 : phiA A v (x : AfE F E) = 1 := by
      simp only [phiA, RingHom.comp_apply, hx _ hne, map_one]
    unfold ordA
    rw [h1, ← map_one (algebraMap (G.P.W v) (G.P.Qq v)), ← Units.val_one]
    exact ordP_unit v 1

end GlobalTheory.TwV.Xc.OrdA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixing
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem unram_comp_normU_of_fix : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  intro Ω _ E _ _ _ _ M _ _ _ _ _ _ A w u h h' _ n ξ a ha H j x hx
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  have h1 : ValuativeRel.valuation (u.adicCompletion M) (x : u.adicCompletion M) = 1 := by
    have : (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion M))
      (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2 hx
  obtain ⟨τ, rfl⟩ := ha'.surj x
  have hdeg : deg τ = 0 := by
    have := ha'.ord_eq τ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at this
    omega
  obtain ⟨t, ht, hd⟩ := GlobalTheory.AboveL.exists_weil_restrict E M Ω A w u h h' τ
  rw [← GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' t τ ht]
  exact H t (hd.2 hdeg) (fun y => by rw [ht]; exact AlgEquiv.commutes _ y) j

end GlobalTheory.RoadU
end

