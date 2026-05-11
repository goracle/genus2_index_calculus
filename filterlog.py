import sys

def filter_walker_log(input_file, output_file):
    try:
        with open(input_file, 'r') as f_in, open(output_file, 'w') as f_out:
            omit_zone = False
            
            for line in f_in:
                # Check for the start of the zone
                if "launching walkers at" in line:
                    f_out.write(line)
                    omit_zone = True
                    continue
                
                # Check for the end of the zone
                if "Walk results" in line:
                    omit_zone = False
                    f_out.write(line)
                    continue
                
                # Print if we are outside the omission zone
                if not omit_zone:
                    f_out.write(line)
                    
    except FileNotFoundError:
        raise FileNotFoundError(f"The file '{input_file}' was not found.")
    except Exception as e:
        raise RuntimeError(f"An error occurred during processing: {e}")

if __name__ == "__main__":
    # Example usage: python script.py input.txt output.txt
    if len(sys.argv) < 2:
        print("Usage: python script.py <filename>")
    else:
        filter_walker_log(sys.argv[1], "filtered_output.txt")
