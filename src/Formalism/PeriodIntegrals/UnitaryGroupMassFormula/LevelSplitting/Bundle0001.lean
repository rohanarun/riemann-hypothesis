module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulVecSpanStable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MeasDefs
section
noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

def PlacesCountable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Countable (HeightOneSpectrum (𝓞 F))

def ContPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)),
    Continuous (fun g : HA (Af F) σ J =>
      ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))

def LatBorel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)),
    MeasurableSet[borel (Fin n → Fv F v ⊗[F] E)] (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))

end PI.LevelKSplit.W.Meas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulInvPiGMemN
section
noncomputable section

namespace PI.LevelKSplit.W.SemiA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub
  rw [mem_stabT]
  intro b
  rw [lin_piG]
  refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · rw [tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · rw [F0, Fin.snoc_last]
      exact SemiG.Dat.unipotent_proj_fixes_normal H _
    · rw [F0, Fin.snoc_castSucc]
      exact SemiG.Dat.Pi_e H _ a
  · rw [tupH, Fin.append_right]
    exact SemiG.Dat.Pi_f H _ b

theorem piG_of_H {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (hg : h ∈ Ssub R σ J P) :
    piG hσσ hJ hP h hg = h := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub at hh
  rw [mem_stabT] at hh
  have he : ∀ a, lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := fun a => by
    have h1 := hh (Fin.castAdd r (Fin.castSucc a))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at h1
  have hz : lin R σ J h (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    have h1 := hh (Fin.castAdd r (Fin.last r))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_last] at h1
  have hf : ∀ a, lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := fun a => by
    have h1 := hh (Fin.natAdd (r + 1) a)
    rwa [tupH, Fin.append_right] at h1
  refine hext fun x => ?_
  rw [lin_piG]
  exact SemiG.Dat.Pi_of_fix H ⟨he, hz⟩ hf (uni_lin h) x

theorem piG_of_N {n : HA R σ J} (hn : n ∈ Nsub R σ J P) (hg : n ∈ Ssub R σ J P) :
    piG hσσ hJ hP n hg = 1 := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  obtain ⟨-, hn2⟩ := hn
  refine hext fun x => ?_
  rw [lin_piG, lin_one]
  refine SemiG.Dat.Pi_of_N H (fun v hv => spanR_le Set.univ (hn2 v fun a => ?_)) x
  have h1 := hv a
  rwa [datR_h] at h1

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ Ssub R σ J P) (hg' : g' ∈ Ssub R σ J P) :
    piG hσσ hJ hP (g * g') ((Ssub R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  refine hext fun x => ?_
  rw [lin_piG, lin_mul, lin_piG, lin_piG, Pi_lin_mul hσσ hJ hP hg hg']
  rfl

theorem mul_inv_piG_mem_N {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    s * (piG hσσ hJ hP s hs)⁻¹ ∈ Nsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  set π := piG hσσ hJ hP s hs with hπ
  have hpe : ∀ b, lin R σ J π (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    rw [hπ, lin_piG]
    exact SemiG.Dat.Pi_e H _ b
  have hpie : ∀ b, lin R σ J π⁻¹ (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    conv_lhs => rw [← hpe b]
    rw [lin_inv_lin]
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, hpie]
    exact S_e hs b
  · set u := lin R σ J π⁻¹ v with hu
    have hu' : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) u = 0 := fun a => by
      rw [datR_h]
      show hR R σ J (ratV (F := F) R (P.e a)) u = 0
      rw [← hR_lin π, hpe, hu, lin_lin_inv]
      exact hv a
    have hZ : lin R σ J s (datR R σ J P T).z - (datR R σ J P T).z ∈
        Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
      spanR_le Set.univ (stabilizer_fixes_tail_coords hs)
    have h1 := SemiG.Dat.N_part H (mapX_S hs) (mapW_S hs) hZ u hu'
    have h2 : (datR R σ J P T).Pi (lin R σ J s) u = v := by
      rw [← lin_piG hσσ hJ hP s hs, ← hπ, hu, lin_lin_inv]
    rw [h2] at h1
    rw [lin_mul, ← hu]
    exact span_le_spanR h1

end R

end PI.LevelKSplit.W.SemiA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.RatVMemSpan
section
noncomputable section

namespace PI.LevelKSplit.W.Glob

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def covR (x : Fin n → E) : Fin n → R ⊗[F] E := fun j => inclR R (∑ i, σ (x i) * J i j)

theorem sigR_inclR (a : E) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (inclR R a) = inclR R (σ a) :=
  DFunLike.congr_fun (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id F R) σ) a

theorem hR_ratV_left (x : Fin n → E) (y : Fin n → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R x) y = covR R σ J x ⬝ᵥ y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, covR, ratV, JR, Matrix.map_apply, sigR_inclR, dotProduct,
    map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_comm

theorem covR_ratV (x y : Fin n → E) :
    covR R σ J x ⬝ᵥ ratV (F := F) R y = inclR R (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [covR, ratV, hE, Formalism.UG.hform, dotProduct, Finset.sum_mul, map_sum, map_mul]
  exact Finset.sum_comm

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i
  simp [ratV]

theorem ratV_smul (c : E) (x : Fin n → E) :
    ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
  funext i
  simp [ratV, smul_eq_mul, map_mul]

theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

variable {R σ J}

theorem ratV_mem_span {m : ℕ} (Y : Fin m → Fin n → E) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Set.range Y)) :
    ratV (F := F) R x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [ratV_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [ratV_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [ratV_smul]; exact Submodule.smul_mem _ _ hy

theorem lin_fix_span (g : HA R σ J) {m : ℕ} (Y : Fin m → Fin n → E)
    (hY : ∀ a, lin R σ J g (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E)
    (hy : y ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a))) :
    lin R σ J g y = y := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hY a
  | zero => exact map_zero _
  | add w w' _ _ hw hw' => rw [map_add (f := _), hw, hw']
  | smul c w _ hw => rw [map_smul, hw]

theorem spanR_univ {m : ℕ} (Y : Fin m → Fin n → E) :
    spanR (F := F) R Y Set.univ =
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  simp only [spanR, Set.image_univ]

theorem hE_swap (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hinv, hJ.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem H_fix_e {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, F0, Fin.append_left, Fin.snoc_castSucc] using hk (Fin.castAdd r (Fin.castSucc a))

theorem H_fix_f {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, Fin.append_right] using hk (Fin.natAdd (r + 1) a)

theorem H_perp {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (w : Fin n → E)
    (hw : ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) (b : Fin r) :
    covR R σ J (P.e b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 ∧
      covR R σ J (P.f b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
  have key : ∀ u : Fin n → E, lin R σ J k (ratV (F := F) R u) = ratV (F := F) R u →
      hE σ J u w = 0 → covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
    intro u hu h0
    calc covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w)
        = hR R σ J (lin R σ J k (ratV (F := F) R u)) (lin R σ J k (ratV (F := F) R w)) := by
          rw [hu, hR_ratV_left]
      _ = hR R σ J (ratV (F := F) R u) (ratV (F := F) R w) := by rw [hR_lin]
      _ = 0 := by rw [hR_ratV_left, covR_ratV, h0, map_zero]
  exact ⟨key _ (H_fix_e P k hk b) (hw b).1, key _ (H_fix_f P k hk b) (hw b).2⟩

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom

theorem phiV_inclR (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    phiV v (inclR (Af F) a) = inclR (Fv F v) a := by
  simp [phiV, inclR]

theorem phiV_ratV (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) :
    (fun i => phiV v (ratV (F := F) (Af F) x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  exact phiV_inclR v (x i)

theorem phiV_cov (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) (y : Fin n → Af F ⊗[F] E) :
    phiV v (covR (Af F) σ J x ⬝ᵥ y) = covR (Fv F v) σ J x ⬝ᵥ fun i => phiV v (y i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul, covR, phiV_inclR]

theorem phiV_span (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (Y : Fin m → Fin n → E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ spanR (F := F) (Af F) Y Set.univ) :
    (fun i => phiV v (y i)) ∈
      Submodule.span (Fv F v ⊗[F] E) (Set.range fun a => ratV (F := F) (Fv F v) (Y a)) := by
  rw [spanR_univ] at hy
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [phiV_ratV]
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero =>
    have h0 : (fun i => phiV v ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := by
      funext i; simp
    rw [h0]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' =>
    have h1 : (fun i => phiV v ((w + w') i)) = (fun i => phiV v (w i)) + fun i => phiV v (w' i) := by
      funext i; simp
    rw [h1]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
    have h1 : (fun i => phiV v ((c • w) i)) = phiV v c • fun i => phiV v (w i) := by
      funext i; simp
    rw [h1]; exact Submodule.smul_mem _ _ hw

theorem compV_mulVec (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J) (x : Fin n → Af F ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (fun i => phiV v (x i)) =
      fun i => phiV v (lin (Af F) σ J g x i) := by
  funext i
  exact (RingHom.map_mulVec (phiV v)
    (HA.mat (R := Af F) (σ := σ) (J := J) g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) x i).symm

theorem mem_Kf (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ ∀ v, ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ := by
  simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply] <;>
    exact Iff.rfl

end Loc

end PI.LevelKSplit.W.Glob
end
end

