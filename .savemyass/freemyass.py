import os
import subprocess

def remove_hooks():
    # Get the root directory (where .git is)
    root_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    hooks_dir = os.path.join(root_dir, '.git', 'hooks')
    
    # Hooks to remove
    hooks = ['pre-commit', 'post-checkout']
    
    for hook in hooks:
        hook_path = os.path.join(hooks_dir, hook)
        if os.path.exists(hook_path):
            print(f"Removing {hook} hook...")
            os.remove(hook_path)
            print(f"Successfully removed {hook} hook")

def decrypt_files():
    try:
        # Get current branch/commit
        current = subprocess.check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD']).decode().strip()
        print(f"\nDecrypting files one last time...")
        # Checkout to same location to trigger existing post-checkout hook
        subprocess.check_call(['git', 'checkout', current])
    except subprocess.CalledProcessError as e:
        print(f"Warning: Failed to decrypt files: {str(e)}")
    except Exception as e:
        print(f"Warning: Unexpected error during decryption: {str(e)}")

def remove_secret():
    secret_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.secret')
    if os.path.exists(secret_file):
        print("Removing passphrase file...")
        os.remove(secret_file)
        print("Successfully removed passphrase")

if __name__ == "__main__":
    try:
        print("\nSaveMyAss Uninstallation")
        print("========================")
        
        response = input("This will remove encryption protection from your assignments. Continue? (y/N): ")
        if response.lower() != 'y':
            print("\nUninstallation cancelled")
            exit(0)
            
        decrypt_files()  # Decrypt first while hooks are still present
        remove_hooks()   # Then remove the hooks
        remove_secret()  # Finally remove the secret file
        
        print("\nUninstallation completed successfully!")
        print("Your files are now unencrypted and will remain that way.")
        print("You can now commit and push them normally.")
        
    except Exception as e:
        print(f"\nError during uninstallation: {str(e)}")
