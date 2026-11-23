module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunction
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.SeamKer

open Formalism.L2.Th1.H

variable {D : D7} {X : Fields}

def seamT (s : Seam D X) (a b : ℕ) : VV D.what₂.Tau a b ≃+ VV X.Tau a b where
  toFun v := fun τ => v (s.iT τ)
  invFun w := fun τ => w (s.iT.symm τ)
  left_inv v := by funext τ; simp
  right_inv w := by funext τ; simp
  map_add' _ _ := rfl

theorem HV_seamT (s : Seam D X) {a b : ℕ} (sc : ℝ) (x y : VV D.what₂.Tau a b) :
    HV sc (seamT s a b x) (seamT s a b y) = HV sc x y := by
  show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, x (s.iT τ) i j * (starRingEnd ℂ) (y (s.iT τ) i j)) =
    (sc : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT (fun τ' => ∑ i, ∑ j, x τ' i j * (starRingEnd ℂ) (y τ' i j))]

theorem alV_seamT (s : Seam D X) {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV D.what₂.Tau a b) :
    alV d sc (seamT s a b x) = alV d sc x := by
  have h := HV_seamT s sc x x
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf, h]

theorem seam_kerTh : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  intro D X s hs cc δ B χ cD a b SS cl N N' Ξ hcc hδ hδ0 hVec hcl hSS hA hDat
  classical
  have hyp := KerMove.split_of_adm _ cl (s.lat N) (s.lat N') B hcc hδ hδ0 hA hcl hSS
  have hI := KerMove.finIdx_of_adm (cc := cc) (δ := δ) (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') hA hcl
  have hθ := KerMove.eNat_fixed (s.lat N) (s.lat N') B χ hcc hδ hVec hA
  have := KerMove.tau_nonempty D
  have hΦ := hDat.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
  have hper := _root_.GlobalTheory.TwV.SeamPer.seamHom_mem_perO s hs B χ cD SS cl N N'
  have hemb := GlobalTheory.T.complexCoordinates_columnFieldIdentification s hs δ (a := a) (b := b)
  have hexp := _root_.GlobalTheory.TwU.SeamExp.expS_seam s hs SS
  have hΛ := hemb.2.2.1 _ _ hper
  have hAh := hemb.2.2.1 _ _ (_root_.GlobalTheory.SeamTwist.seamHom_mem_twO s _ _ hper cl (fun Q => -expS SS Q)
    (fun Q => -expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) Q)
    (fun P => by simp only [hexp]))
  have hBh := hemb.2.2.1 _ _ (_root_.GlobalTheory.SeamTwist.seamHom_mem_twO s _ _ hper cl (expS SS)
    (expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) hexp)
  have hdat : onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) = fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v) :=
    funext fun v => (hemb.2.2.2 hδ0 Ξ v).symm
  have hvec : B.eNat χ a b (s.lat N) (s.lat N') = fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v) := by
    funext v
    show B.eNat χ a b (s.lat N) (s.lat N') v = B.eNat χ a b (s.lat N) (s.lat N') (fun τ => v (s.iT (s.iT.symm τ)))
    simp only [Equiv.apply_symm_apply]
  have hθ' : (fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v)) ∈ fixedBy _ _ _ := hvec ▸ hθ
  have hΦ' : InvOn _ _ (fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v)) := hdat ▸ hΦ
  funext z
  unfold Seam.push kerTh thC xiV
  rw [hdat, hvec]
  exact _root_.GlobalTheory.TwU.XiTwo.xiL_two _ _ _ _ (seamT s a b) (HV_seamT s _) (alV_seamT s _ _) _ _ _ _ _ _ hyp hΛ hAh hBh
    ⟨_, repsOf_spec _ _ hI.1⟩ ⟨_, repsOf_spec _ _ hI.2.1⟩ ⟨_, repsOf_spec _ _ hI.2.2⟩ 1 _ _ hθ' hΦ' z

end GlobalTheory.TwU.SeamKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeTrueColumnBaseLatticeEqStandard
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.BaseComp
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem star_int (r : 𝓞 E) : ∃ s : 𝓞 E, (s : E) = star (r : E) :=
  ⟨⟨star (r : E), r.2.map (starRingEnd E).toIntAlgHom⟩, rfl⟩

theorem mem_dual_iff (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) L ↔ ∀ x ∈ L, (∑ k, star (x k) * y k) ∈ (algebraMap (𝓞 E) E).range := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

theorem fg_of_int (L : Submodule (𝓞 E) (Fin n → E)) (h : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) : L.FG := by
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) := LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  have hle : L ≤ LinearMap.range f := by
    intro x hx
    choose r hr using h x hx
    exact ⟨r, funext fun j => (hr j).symm⟩
  haveI : IsNoetherian (𝓞 E) (LinearMap.range f) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have := (isNoetherian_submodule.1 (inferInstance : IsNoetherian (𝓞 E) (LinearMap.range f))) L hle
  exact this

theorem sup_dual_eq_std (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E))
    (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    Lb ⊔ Ideal.span {c} • Formalism.HermitianLatticesTheory.dual (hStd E n) Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  have hst : star (t : E) ≠ 0 := by
    rw [star_ne_zero]; exact_mod_cast ht
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro x hx
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
      exact ⟨r, hr.symm⟩
    · rw [Submodule.smul_le]
      intro a ha y hy
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
      intro j
      have hx : (Pi.single j (t : E) : Fin n → E) ∈ Lb := by
        rw [hLb]
        intro k
        by_cases hk : k = j
        · subst hk; exact ⟨t, by simp, fun _ => dvd_refl t⟩
        · exact ⟨0, by simp [hk], fun _ => dvd_zero t⟩
      obtain ⟨r, hr⟩ := (mem_dual_iff Lb y).1 hy _ hx
      have hsum : ∑ k, star ((Pi.single j (t : E) : Fin n → E) k) * y k = star (t : E) * y j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      rw [hsum] at hr
      refine ⟨s * r, ?_⟩
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hr]
      rw [show algebraMap (𝓞 E) E c = (c : E) from rfl, hc, mul_assoc]
  · intro x hx
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one] at hx
    choose r hr using hx
    let x' : Fin n → E := fun j => if j.1 + 1 = n then 0 else x j
    let w : Fin n → E := fun j => if j.1 + 1 = n then x j / star (t : E) else 0
    have hx' : x' ∈ Lb := by
      rw [hLb]
      intro j
      by_cases hj : j.1 + 1 = n
      · exact ⟨0, by simp [x', hj], fun _ => dvd_zero t⟩
      · exact ⟨r j, by simp [x', hj, hr j], fun h => absurd h hj⟩
    have hw : w ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) Lb := by
      rw [mem_dual_iff]
      intro z hz
      refine Subring.sum_mem _ fun k _ => ?_
      by_cases hk : k.1 + 1 = n
      · obtain ⟨q, hq, hdiv⟩ := (hLb z).1 hz k
        obtain ⟨d, rfl⟩ := hdiv hk
        obtain ⟨s, hs⟩ := star_int d
        refine ⟨s * r k, ?_⟩
        simp only [w, hk, if_true, hq]
        rw [map_mul, hr k, show algebraMap (𝓞 E) E s = (s : E) from rfl, hs]
        push_cast
        rw [star_mul', ← hr k]
        field_simp
      · exact ⟨0, by simp [w, hk]⟩
    have hxe : x = x' + c • w := by
      funext j
      by_cases hj : j.1 + 1 = n
      · simp only [x', w, hj, if_true, Pi.add_apply, Pi.smul_apply, zero_add]
        rw [Algebra.smul_def, show algebraMap (𝓞 E) E c = (c : E) from rfl, hc]
        field_simp
      · simp [x', w, hj]
    rw [hxe]
    exact Submodule.add_mem_sup hx' (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hw)

end GlobalTheory.TwU.BaseComp

open scoped TensorProduct

namespace GlobalTheory.TwU.BaseComp

theorem latCo_one_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (sp : Spaces R F E) (hσ : ∀ x, (sp.cm.sig : E →+* E) x = star x) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (t c : 𝓞 E) (ht : t ≠ 0) (hc : (c : E) = star (t : E)) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → t ∣ r)) :
    GlobalTheory.TwU.latCo sp J 1 c 1 Lb = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  subst hJ
  have hfg : Lb.FG := fg_of_int Lb fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have hA : Formalism.L2.PairingIndexBounds.F.latAd (F := F) (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb :=
    GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ Lb Lb (Module.Finite.iff_fg.2 hfg) (fun x => by simp)
  unfold GlobalTheory.TwU.latCo
  rw [hA]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual ((sp.cm.sig : E →+* E)) hσ Lb
  unfold dualL at key
  erw [key]
  exact sup_dual_eq_std t c ht hc Lb hLb

end GlobalTheory.TwU.BaseComp


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.TwU.latCo_base_eq_stdL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), (∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N i) (X.piT u)) → GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) 1 Lb = StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i) := by
  intro B X I hI hP l Z u i hi Lb hLb
  have hG : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have ht : X.piT u ≠ 0 := by
    intro h0
    have hc := l.pr.piT_cop u
    have h0' : (B.primes X).piT u = 0 := h0
    rw [h0', map_zero] at hc
    exact not_isCoprime_zero_zero hc
  exact GlobalTheory.TwU.BaseComp.latCo_one_base _ (fun x => rfl) _ hG (X.piT u) (B.fields.conjO (X.piT u)) ht rfl Lb hLb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepChartLevelAtBadPrimes
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplLev

theorem cong_of_nearAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g₁ g₂ : GL (Fin N) E)
    (hn : 0 < n) (h₁ : NearAt P n x g₁) (h₂ : NearAt P n x g₂) (a b : Fin N) :
    IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (((g₁⁻¹ * g₂ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) :=
  _root_.GlobalTheory.TwU.CongTwo.intAt_inv_mul_of_nearAt P n x g₁ g₂ hn h₁ h₂ a b

theorem cong_seam {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (g : Sp X.E N ≃ₗ[X.E] Sp X.E N)
    (h : ∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ *
      (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) :
    ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) :=
  GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence s P n g h

section Cong1

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col

theorem cong_mem_level_chr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX.ok hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := _root_.GlobalTheory.QCong.conj_extE_cong P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := _root_.GlobalTheory.QCong.conj_extE_cong P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine _root_.GlobalTheory.ParahoricOfCong.mem_JQ_of_cong P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact _root_.GlobalTheory.LamQBCong.lamQB_eq_one_of_cong P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

end Cong1

section Lift

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem levAt_mul {n : ℕ} {Λ : LevFam X.E X.K n Pr.vGs} {Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))} {P : rowSG Pr sel mu}
    {κ κ₂ : GLint X.E n P.1} {c c₂ : X.Kˣ} (h : LevAt Λ Θ P κ c) (h₂ : LevAt Λ Θ P κ₂ c₂) : LevAt Λ Θ P (κ * κ₂) (c * c₂) := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · obtain ⟨h1, e1⟩ := h.1 hP
    obtain ⟨h2, e2⟩ := h₂.1 hP
    refine ⟨by rw [map_mul]; exact mul_mem h1 h2, ?_⟩
    rw [e1, e2, ← map_mul]
    exact congrArg _ (Subtype.ext (map_mul _ _ _).symm)
  · obtain ⟨h1, e1⟩ := h.2 hQ hP
    obtain ⟨h2, e2⟩ := h₂.2 hQ hP
    exact ⟨mul_mem h1 h2, by rw [e1, e2, ← map_mul]; rfl⟩

theorem levAt_of_lift (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (b : L.β j) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N j) P.1)
    (r : AutY X R j) (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P))
    (hrx : ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (κ.1 x)) :
    ∃ c : X.Kˣ, LevAt (L.levG j b) (L.levQ j b) P κ c ∧ (c : X.K) = chiInv Ch sel mu cst j P (L.h j b P) r := by
  by_cases hP : P.1 ∈ Pr.vGs
  · have hmem : GlobalTheory.TopStep.redGL _ P.1 κ ∈ (L.levG j b ⟨P.1, hP⟩).H :=
      (hL.grpG j b ⟨P.1, hP⟩ _).2 ⟨κ.1, ⟨r, hr, hrx⟩, fun x hx => GlobalTheory.TopStep.redV_redGL κ hx⟩
    refine ⟨(L.levG j b ⟨P.1, hP⟩).lam ⟨_, hmem⟩, ⟨fun hP' => ⟨hmem, rfl⟩, fun _ hP' => absurd hP hP'⟩, ?_⟩
    exact hL.chrG j b ⟨P.1, hP⟩ ⟨_, hmem⟩ κ.1 r hr hrx fun x hx => GlobalTheory.TopStep.redV_redGL κ hx
  · have hQ := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    have hmem : κ ∈ (L.levQ j b ⟨P.1, hQ⟩).H := by
      rw [hL.grpQ, Subgroup.mem_subgroupOf]
      exact ⟨r, hr, hrx⟩
    refine ⟨(L.levQ j b ⟨P.1, hQ⟩).lam ⟨κ, hmem⟩, ⟨fun hP' => absurd hP' hP, fun _ _ => ⟨hmem, rfl⟩⟩, ?_⟩
    exact hL.chrQ j b ⟨P.1, hQ⟩ ⟨κ, hmem⟩ r hr hrx

end Lift

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem levAt_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (β' : (St (t.m2 + 1) (cpl_lt t μ).le).Ch)
    (κ' : ((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
    (∀ P, InFrame t.seam (A.fb (t.m2 + 1) (cpl_lt t μ).le β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) →
    ∃ c : SB t μ → t.X.Kˣ,
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
        ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P) (c P)) ∧
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = ((((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.chi κ' : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β' κ' κ'' hfr
  classical
  have hL := t.idx_ok μ
  have hC := hTie.levCpl β'
  have hU := (((St (t.m2 + 1) (cpl_lt t μ).le).K β').lev.U_eq κ'.1).1 κ'.2
  have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
    intro P
    unfold IsOver
    rw [HeightOneSpectrum.under_asIdeal]
  choose g zz hg using fun P : SB t μ => hC.1 P _ (hov P) κ'.1 hU.1 (hU.2 _)
  have hchi := hC.2.2 κ' g zz hg
  have key : ∀ P : SB t μ, ∃ c : t.X.Kˣ, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β'))
      ((t.idx μ).levQ (t.m2 + 1) (A.ib (t.m2 + 1) (cpl_lt t μ) β')) P (κ'' P)⁻¹ c ∧ (c : t.X.K) = zz P := by
    intro P
    obtain ⟨⟨r, hr, hrx, hz⟩, -⟩ := (hg P).1
    have hgint : g P ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := hL.int _ _ P ⟨r, hr, hrx⟩
    set κg : GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := ⟨g P, hgint⟩ with hκg
    set k : GLint t.X.E (D.R.N (t.m2 + 1)) P.1 := κg⁻¹ * (κ'' P)⁻¹ with hk
    have hcg := cong_of_nearAt (seamP t.seam P.1) ((t.cst μ).D P) _ _ _ (hL.cst_ok.D_pos P) (hg P).2 (hfr P)
    rw [← map_inv, ← map_mul] at hcg
    have hk1 := cong_seam t.seam P.1 ((t.cst μ).D P) k.1 hcg
    obtain ⟨rk, hrk, hrkx, hchik⟩ := cong_mem_level_chr_one t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hPin.fields t.pr_ok hL
      (t.m2 + 1) le_rfl (A.ib (t.m2 + 1) (cpl_lt t μ) β') P k.1 hk1
    obtain ⟨c1, hl1, hc1⟩ := levAt_of_lift hL (A.ib (t.m2 + 1) (cpl_lt t μ) β') P κg r hr hrx
    obtain ⟨c2, hl2, hc2⟩ := levAt_of_lift hL (A.ib (t.m2 + 1) (cpl_lt t μ) β') P k rk hrk hrkx
    have e : κg * k = (κ'' P)⁻¹ := by rw [hk, mul_inv_cancel_left]
    refine ⟨c1 * c2, e ▸ levAt_mul hl1 hl2, ?_⟩
    rw [Units.val_mul, hc1, hc2, hchik, mul_one, hz]
  choose c hc hcv using key
  refine ⟨fun P => (c P)⁻¹, fun P => by have h := (hc P).inv; rwa [inv_inv] at h, ?_⟩
  have e1 : ((∏ P, (c P)⁻¹ : t.X.Kˣ) : t.X.K) = (∏ P, zz P)⁻¹ := by
    rw [Units.coe_prod, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun P _ => by rw [Units.val_inv_eq_inv_val, hcv P]
  have e2 := eq_inv_of_mul_eq_one_left hchi
  have e3 : t.seam.σ₀ ((∏ P, (c P)⁻¹ : t.X.Kˣ) : t.X.K) = (t.seam.σ₀ (∏ P, zz P))⁻¹ := by
    rw [e1, map_inv₀]
  exact e3.trans e2.symm

end Main

end GlobalTheory.CplLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatr
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwU.UnitaryFrom

theorem exists_uf_seamGL_eq : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {n : ℕ} (G : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (G : Matrix (Fin n) (Fin n) D.host.E) * (G : Matrix (Fin n) (Fin n) D.host.E) = 1 → ∃ g : UF X.E n, seamGL s g.1 = G := by
  intro D X s hs n G hG
  have hconj : ∀ a : D.host.E, s.iE.symm (D.host.conj a) = star (s.iE.symm a) := by
    intro a
    apply s.iE.injective
    rw [RingEquiv.apply_symm_apply, hs.2, RingEquiv.apply_symm_apply]
  have hsig : ∀ a : D.host.E, (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) a = D.host.conj a :=
    fun a => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D a
  let Gx : GL (Fin n) X.E := bc (s.iE.symm : D.host.E →+* X.E) G
  let M : Matrix (Fin n) (Fin n) X.E := (G : Matrix (Fin n) (Fin n) D.host.E).map s.iE.symm
  have hMM : Mᴴ * M = 1 := by
    ext i j
    have h := congrArg s.iE.symm (congrFun (congrFun hG i) j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      hsig, hconj] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, M, Matrix.map_apply]
    rw [h]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij]
  let g : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E) (Matrix.GeneralLinearGroup.toLin Gx)
  have hg : ∀ x, g x = M *ᵥ x := by
    intro x
    rfl
  refine ⟨⟨g, ?_⟩, ?_⟩
  · intro x y
    rw [hStd_apply, hStd_apply, hg, hg]
    have h1 : (∑ i, star ((M *ᵥ x) i) * (M *ᵥ y) i) = star (M *ᵥ x) ⬝ᵥ (M *ᵥ y) := rfl
    have h2 : (∑ i, star (x i) * y i) = star x ⬝ᵥ y := rfl
    rw [h1, h2, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hMM,
      Matrix.vecMul_one]
  · apply Units.ext
    show (((seamGL s) g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = G
    ext i j
    simp [seamGL, bc, g, Gx]

end GlobalTheory.TwU.UnitaryFrom
end

