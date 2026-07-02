# check_current_setup.py
import torch
import subprocess
import sys

def check_current_setup():
    print("=" * 60)
    print("PyTorch Installation Check")
    print("=" * 60)
    
    # 1. PyTorch version
    print(f"PyTorch version: {torch.__version__}")
    
    # 2. CUDA availability
    print(f"CUDA available: {torch.cuda.is_available()}")
    
    if torch.cuda.is_available():
        print(f"CUDA version: {torch.version.cuda}")
        print(f"GPU: {torch.cuda.get_device_name(0)}")
        print(f"VRAM: {torch.cuda.get_device_properties(0).total_memory / 1e9:.2f} GB")
        print("✅ GPU is working!")
        return True
    else:
        print("❌ GPU NOT working")
        return False

if __name__ == "__main__":
    has_gpu = check_current_setup()
    
    if not has_gpu:
        print("\n💡 Solutions:")
        print("1. Install CUDA version: pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu118")
        print("2. Or use conda: conda install pytorch torchvision torchaudio pytorch-cuda=11.8 -c pytorch -c nvidia")
        print("3. Don't remove existing PyTorch, install in new environment")